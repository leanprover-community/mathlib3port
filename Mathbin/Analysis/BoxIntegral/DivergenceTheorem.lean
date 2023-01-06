/-
Copyright (c) 2021 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov

! This file was ported from Lean 3 source module analysis.box_integral.divergence_theorem
! leanprover-community/mathlib commit 26f081a2fb920140ed5bc5cc5344e84bcc7cb2b2
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Analysis.BoxIntegral.Basic
import Mathbin.Analysis.BoxIntegral.Partition.Additive
import Mathbin.Analysis.Calculus.Fderiv

/-!
# Divergence integral for Henstock-Kurzweil integral

In this file we prove the Divergence Theorem for a Henstock-Kurzweil style integral. The theorem
says the following. Let `f : ℝⁿ → Eⁿ` be a function differentiable on a closed rectangular box
`I` with derivative `f' x : ℝⁿ →L[ℝ] Eⁿ` at `x ∈ I`. Then the divergence `λ x, ∑ k, f' x eₖ k`,
where `eₖ = pi.single k 1` is the `k`-th basis vector, is integrable on `I`, and its integral is
equal to the sum of integrals of `f` over the faces of `I` taken with appropriate signs.

To make the proof work, we had to ban tagged partitions with “long and thin” boxes. More precisely,
we use the following generalization of one-dimensional Henstock-Kurzweil integral to functions
defined on a box in `ℝⁿ` (it corresponds to the value `box_integral.integration_params.GP = ⊥` of
`box_integral.integration_params` in the definition of `box_integral.has_integral`).

We say that `f : ℝⁿ → E` has integral `y : E` over a box `I ⊆ ℝⁿ` if for an arbitrarily small
positive `ε` and an arbitrarily large `c`, there exists a function `r : ℝⁿ → (0, ∞)` such that for
any tagged partition `π` of `I` such that

* `π` is a Henstock partition, i.e., each tag belongs to its box;
* `π` is subordinate to `r`;
* for every box of `π`, the maximum of the ratios of its sides is less than or equal to `c`,

the integral sum of `f` over `π` is `ε`-close to `y`. In case of dimension one, the last condition
trivially holds for any `c ≥ 1`, so this definition is equivalent to the standard definition of
Henstock-Kurzweil integral.

## Tags

Henstock-Kurzweil integral, integral, Stokes theorem, divergence theorem
-/


open Classical BigOperators Nnreal Ennreal TopologicalSpace BoxIntegral

open ContinuousLinearMap (lsmul)

open Filter Set Finset Metric

open BoxIntegral.IntegrationParams (gP GP_le)

noncomputable section

universe u

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E] {n : ℕ}

namespace BoxIntegral

-- mathport name: «exprℝⁿ»
local notation "ℝⁿ" => Fin n → ℝ

-- mathport name: «exprℝⁿ⁺¹»
local notation "ℝⁿ⁺¹" => Fin (n + 1) → ℝ

-- mathport name: «exprEⁿ⁺¹»
local notation "Eⁿ⁺¹" => Fin (n + 1) → E

variable [CompleteSpace E] (I : Box (Fin (n + 1))) {i : Fin (n + 1)}

open MeasureTheory

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers
      [(Command.docComment "/--" "Auxiliary lemma for the divergence theorem. -/")]
      []
      []
      []
      []
      [])
     (Command.theorem
      "theorem"
      (Command.declId `norm_volume_sub_integral_face_upper_sub_lower_smul_le [])
      (Command.declSig
       [(Term.implicitBinder
         "{"
         [`f]
         [":"
          (Term.arrow
           (BoxIntegral.Analysis.BoxIntegral.DivergenceTheorem.«termℝⁿ⁺¹» "ℝⁿ⁺¹")
           "→"
           `E)]
         "}")
        (Term.implicitBinder
         "{"
         [`f']
         [":"
          (Topology.Algebra.Module.Basic.«term_→L[_]_»
           (BoxIntegral.Analysis.BoxIntegral.DivergenceTheorem.«termℝⁿ⁺¹» "ℝⁿ⁺¹")
           " →L["
           (Data.Real.Basic.termℝ "ℝ")
           "] "
           `E)]
         "}")
        (Term.explicitBinder
         "("
         [`hfc]
         [":" (Term.app `ContinuousOn [`f (Term.proj `I "." `IccCat)])]
         []
         ")")
        (Term.implicitBinder
         "{"
         [`x]
         [":" (BoxIntegral.Analysis.BoxIntegral.DivergenceTheorem.«termℝⁿ⁺¹» "ℝⁿ⁺¹")]
         "}")
        (Term.explicitBinder "(" [`hxI] [":" («term_∈_» `x "∈" (Term.proj `I "." `IccCat))] [] ")")
        (Term.implicitBinder "{" [`a] [":" `E] "}")
        (Term.implicitBinder "{" [`ε] [":" (Data.Real.Basic.termℝ "ℝ")] "}")
        (Term.explicitBinder "(" [`h0] [":" («term_<_» (num "0") "<" `ε)] [] ")")
        (Term.explicitBinder
         "("
         [`hε]
         [":"
          (Std.ExtendedBinder.«term∀__,_»
           "∀"
           (Lean.binderIdent `y)
           («binderTerm∈_» "∈" (Term.proj `I "." `IccCat))
           ","
           («term_≤_»
            (Analysis.Normed.Group.Basic.«term‖_‖»
             "‖"
             («term_-_»
              («term_-_» (Term.app `f [`y]) "-" `a)
              "-"
              (Term.app `f' [(«term_-_» `y "-" `x)]))
             "‖")
            "≤"
            («term_*_»
             `ε
             "*"
             (Analysis.Normed.Group.Basic.«term‖_‖» "‖" («term_-_» `y "-" `x) "‖"))))]
         []
         ")")
        (Term.implicitBinder "{" [`c] [":" (Nnreal.Data.Real.Nnreal.nnreal "ℝ≥0")] "}")
        (Term.explicitBinder
         "("
         [`hc]
         [":" («term_≤_» (Term.proj `I "." `distortion) "≤" `c)]
         []
         ")")]
       (Term.typeSpec
        ":"
        («term_≤_»
         (Analysis.Normed.Group.Basic.«term‖_‖»
          "‖"
          («term_-_»
           (Algebra.Group.Defs.«term_•_»
            (BigOperators.Algebra.BigOperators.Basic.finset.prod_univ
             "∏"
             (Std.ExtendedBinder.extBinders (Std.ExtendedBinder.extBinder (Lean.binderIdent `j) []))
             ", "
             («term_-_»
              (Term.app (Term.proj `I "." `upper) [`j])
              "-"
              (Term.app (Term.proj `I "." `lower) [`j])))
            " • "
            (Term.app `f' [(Term.app `Pi.single [`i (num "1")])]))
           "-"
           («term_-_»
            (Term.app
             `integral
             [(Term.app (Term.proj `I "." `face) [`i])
              (Order.BoundedOrder.«term⊥» "⊥")
              («term_∘_»
               `f
               "∘"
               (Term.app (Term.proj `i "." `insertNth) [(Term.app (Term.proj `I "." `upper) [`i])]))
              `BoxAdditiveMap.volume])
            "-"
            (Term.app
             `integral
             [(Term.app (Term.proj `I "." `face) [`i])
              (Order.BoundedOrder.«term⊥» "⊥")
              («term_∘_»
               `f
               "∘"
               (Term.app (Term.proj `i "." `insertNth) [(Term.app (Term.proj `I "." `lower) [`i])]))
              `BoxAdditiveMap.volume])))
          "‖")
         "≤"
         («term_*_»
          («term_*_» («term_*_» (num "2") "*" `ε) "*" `c)
          "*"
          (BigOperators.Algebra.BigOperators.Basic.finset.prod_univ
           "∏"
           (Std.ExtendedBinder.extBinders (Std.ExtendedBinder.extBinder (Lean.binderIdent `j) []))
           ", "
           («term_-_»
            (Term.app (Term.proj `I "." `upper) [`j])
            "-"
            (Term.app (Term.proj `I "." `lower) [`j])))))))
      (Command.declValSimple
       ":="
       (Term.byTactic
        "by"
        (Tactic.tacticSeq
         (Tactic.tacticSeq1Indented
          [(Tactic.tacticHave_
            "have"
            (Term.haveDecl
             (Term.haveIdDecl
              [`Hl []]
              [(Term.typeSpec
                ":"
                («term_∈_»
                 (Term.app `I.lower [`i])
                 "∈"
                 (Term.app `Icc [(Term.app `I.lower [`i]) (Term.app `I.upper [`i])])))]
              ":="
              (Term.app
               (Term.proj `Set.left_mem_Icc "." (fieldIdx "2"))
               [(Term.app `I.lower_le_upper [`i])]))))
           []
           (Tactic.tacticHave_
            "have"
            (Term.haveDecl
             (Term.haveIdDecl
              [`Hu []]
              [(Term.typeSpec
                ":"
                («term_∈_»
                 (Term.app `I.upper [`i])
                 "∈"
                 (Term.app `Icc [(Term.app `I.lower [`i]) (Term.app `I.upper [`i])])))]
              ":="
              (Term.app
               (Term.proj `Set.right_mem_Icc "." (fieldIdx "2"))
               [(Term.app `I.lower_le_upper [`i])]))))
           []
           (Tactic.tacticHave_
            "have"
            (Term.haveDecl
             (Term.haveIdDecl
              [`Hi []]
              [(Term.typeSpec
                ":"
                (Std.ExtendedBinder.«term∀__,_»
                 "∀"
                 (Lean.binderIdent `x)
                 («binderTerm∈_»
                  "∈"
                  (Term.app `Icc [(Term.app `I.lower [`i]) (Term.app `I.upper [`i])]))
                 ","
                 (Term.app
                  (Term.explicitUniv `Integrable ".{" [(num "0") "," `u "," `u] "}")
                  [(Term.app `I.face [`i])
                   (Order.BoundedOrder.«term⊥» "⊥")
                   («term_∘_» `f "∘" (Term.app `i.insert_nth [`x]))
                   `box_additive_map.volume])))]
              ":="
              (Term.fun
               "fun"
               (Term.basicFun
                [`x `hx]
                []
                "=>"
                (Term.app
                 `integrable_of_continuous_on
                 [(Term.hole "_") (Term.app `box.continuous_on_face_Icc [`hfc `hx]) `volume]))))))
           []
           (Tactic.tacticHave_
            "have"
            (Term.haveDecl
             (Term.haveIdDecl
              []
              [(Term.typeSpec
                ":"
                (Std.ExtendedBinder.«term∀__,_»
                 "∀"
                 (Lean.binderIdent `y)
                 («binderTerm∈_» "∈" (Term.proj (Term.app `I.face [`i]) "." `IccCat))
                 ","
                 («term_≤_»
                  (Analysis.Normed.Group.Basic.«term‖_‖»
                   "‖"
                   («term_-_»
                    (Term.app
                     `f'
                     [(Term.app
                       `Pi.single
                       [`i («term_-_» (Term.app `I.upper [`i]) "-" (Term.app `I.lower [`i]))])])
                    "-"
                    («term_-_»
                     (Term.app `f [(Term.app `i.insert_nth [(Term.app `I.upper [`i]) `y])])
                     "-"
                     (Term.app `f [(Term.app `i.insert_nth [(Term.app `I.lower [`i]) `y])])))
                   "‖")
                  "≤"
                  («term_*_» («term_*_» (num "2") "*" `ε) "*" (Term.app `diam [`I.Icc])))))]
              ":="
              (Term.byTactic
               "by"
               (Tactic.tacticSeq
                (Tactic.tacticSeq1Indented
                 [(Tactic.intro "intro" [`y `hy])
                  []
                  (Mathlib.Tactic.set
                   "set"
                   []
                   (Mathlib.Tactic.setArgsRest
                    `g
                    []
                    ":="
                    (Term.fun
                     "fun"
                     (Term.basicFun
                      [`y]
                      []
                      "=>"
                      («term_-_»
                       («term_-_» (Term.app `f [`y]) "-" `a)
                       "-"
                       (Term.app `f' [(«term_-_» `y "-" `x)]))))
                    ["with" [] `hg]))
                  []
                  (Tactic.change
                   "change"
                   (Std.ExtendedBinder.«term∀__,_»
                    "∀"
                    (Lean.binderIdent `y)
                    («binderTerm∈_» "∈" `I.Icc)
                    ","
                    («term_≤_»
                     (Analysis.Normed.Group.Basic.«term‖_‖» "‖" (Term.app `g [`y]) "‖")
                     "≤"
                     («term_*_»
                      `ε
                      "*"
                      (Analysis.Normed.Group.Basic.«term‖_‖» "‖" («term_-_» `y "-" `x) "‖"))))
                   [(Tactic.location "at" (Tactic.locationHyp [`hε] []))])
                  []
                  (Tactic.clearValue "clear_value" [(group `g)])
                  []
                  (Std.Tactic.obtain
                   "obtain"
                   [(Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `rfl)])]
                   [":"
                    («term_=_»
                     `f
                     "="
                     (Term.fun
                      "fun"
                      (Term.basicFun
                       [`y]
                       []
                       "=>"
                       («term_+_»
                        («term_+_» `a "+" (Term.app `f' [(«term_-_» `y "-" `x)]))
                        "+"
                        (Term.app `g [`y])))))]
                   [":="
                    [(Term.byTactic
                      "by"
                      (Tactic.tacticSeq
                       (Tactic.tacticSeq1Indented
                        [(Tactic.simp
                          "simp"
                          []
                          []
                          []
                          ["[" [(Tactic.simpLemma [] [] `hg)] "]"]
                          [])])))]])
                  []
                  (convertTo
                   "convert_to"
                   («term_≤_»
                    (Analysis.Normed.Group.Basic.«term‖_‖»
                     "‖"
                     («term_-_»
                      (Term.app `g [(Term.app `i.insert_nth [(Term.app `I.lower [`i]) `y])])
                      "-"
                      (Term.app `g [(Term.app `i.insert_nth [(Term.app `I.upper [`i]) `y])]))
                     "‖")
                    "≤"
                    (Term.hole "_"))
                   [])
                  []
                  (tactic__
                   (cdotTk (patternIgnore (token.«· » "·")))
                   [(Tactic.congr "congr" [(num "1")])
                    []
                    (Tactic.tacticHave_
                     "have"
                     (Term.haveDecl
                      (Term.haveIdDecl
                       []
                       []
                       ":="
                       (Term.app
                        `Fin.insert_nth_sub_same
                        [`i (Term.app `I.upper [`i]) (Term.app `I.lower [`i]) `y]))))
                    []
                    (Tactic.simp
                     "simp"
                     []
                     []
                     ["only"]
                     ["["
                      [(Tactic.simpLemma [] [(patternIgnore (token.«← » "←"))] `this)
                       ","
                       (Tactic.simpLemma [] [] `f'.map_sub)]
                      "]"]
                     [])
                    []
                    (Tactic.abel "abel" [] [])])
                  []
                  (tactic__
                   (cdotTk (patternIgnore (token.«· » "·")))
                   [(Tactic.tacticHave_
                     "have"
                     (Term.haveDecl
                      (Term.haveIdDecl
                       []
                       [(Term.typeSpec
                         ":"
                         (Std.ExtendedBinder.«term∀__,_»
                          "∀"
                          (Lean.binderIdent `z)
                          («binderTerm∈_»
                           "∈"
                           (Term.app `Icc [(Term.app `I.lower [`i]) (Term.app `I.upper [`i])]))
                          ","
                          («term_∈_» (Term.app `i.insert_nth [`z `y]) "∈" `I.Icc)))]
                       ":="
                       (Term.fun
                        "fun"
                        (Term.basicFun
                         [`z `hz]
                         []
                         "=>"
                         (Term.app `I.maps_to_insert_nth_face_Icc [`hz `hy]))))))
                    []
                    (Mathlib.Tactic.replace'
                     "replace"
                     [`hε []]
                     [(Term.typeSpec
                       ":"
                       (Std.ExtendedBinder.«term∀__,_»
                        "∀"
                        (Lean.binderIdent `y)
                        («binderTerm∈_» "∈" `I.Icc)
                        ","
                        («term_≤_»
                         (Analysis.Normed.Group.Basic.«term‖_‖» "‖" (Term.app `g [`y]) "‖")
                         "≤"
                         («term_*_» `ε "*" (Term.app `diam [`I.Icc])))))])
                    []
                    (tactic__
                     (cdotTk (patternIgnore (token.«· » "·")))
                     [(Tactic.intro "intro" [`y `hy])
                      []
                      (Tactic.refine'
                       "refine'"
                       (Term.app
                        (Term.proj (Term.app `hε [`y `hy]) "." `trans)
                        [(Term.app `mul_le_mul_of_nonneg_left [(Term.hole "_") `h0.le])]))
                      []
                      (Tactic.rwSeq
                       "rw"
                       []
                       (Tactic.rwRuleSeq
                        "["
                        [(Tactic.rwRule [(patternIgnore (token.«← » "←"))] `dist_eq_norm)]
                        "]")
                       [])
                      []
                      (Tactic.exact
                       "exact"
                       (Term.app `dist_le_diam_of_mem [`I.is_compact_Icc.bounded `hy `hxI]))])
                    []
                    (Tactic.rwSeq
                     "rw"
                     []
                     (Tactic.rwRuleSeq
                      "["
                      [(Tactic.rwRule [] `two_mul) "," (Tactic.rwRule [] `add_mul)]
                      "]")
                     [])
                    []
                    (Tactic.exact
                     "exact"
                     (Term.app
                      `norm_sub_le_of_le
                      [(Term.app `hε [(Term.hole "_") (Term.app `this [(Term.hole "_") `Hl])])
                       (Term.app
                        `hε
                        [(Term.hole "_") (Term.app `this [(Term.hole "_") `Hu])])]))])]))))))
           []
           (calcTactic
            "calc"
            (calcStep
             («term_=_»
              (Analysis.Normed.Group.Basic.«term‖_‖»
               "‖"
               («term_-_»
                (Algebra.Group.Defs.«term_•_»
                 (BigOperators.Algebra.BigOperators.Basic.finset.prod_univ
                  "∏"
                  (Std.ExtendedBinder.extBinders
                   (Std.ExtendedBinder.extBinder (Lean.binderIdent `j) []))
                  ", "
                  («term_-_» (Term.app `I.upper [`j]) "-" (Term.app `I.lower [`j])))
                 " • "
                 (Term.app `f' [(Term.app `Pi.single [`i (num "1")])]))
                "-"
                («term_-_»
                 (Term.app
                  `integral
                  [(Term.app `I.face [`i])
                   (Order.BoundedOrder.«term⊥» "⊥")
                   («term_∘_» `f "∘" (Term.app `i.insert_nth [(Term.app `I.upper [`i])]))
                   `box_additive_map.volume])
                 "-"
                 (Term.app
                  `integral
                  [(Term.app `I.face [`i])
                   (Order.BoundedOrder.«term⊥» "⊥")
                   («term_∘_» `f "∘" (Term.app `i.insert_nth [(Term.app `I.lower [`i])]))
                   `box_additive_map.volume])))
               "‖")
              "="
              (Analysis.Normed.Group.Basic.«term‖_‖»
               "‖"
               (Term.app
                (Term.explicitUniv `integral ".{" [(num "0") "," `u "," `u] "}")
                [(Term.app `I.face [`i])
                 (Order.BoundedOrder.«term⊥» "⊥")
                 (Term.fun
                  "fun"
                  (Term.basicFun
                   [`x]
                   [(Term.typeSpec
                     ":"
                     (Term.arrow (Term.app `Fin [`n]) "→" (Data.Real.Basic.termℝ "ℝ")))]
                   "=>"
                   («term_-_»
                    (Term.app
                     `f'
                     [(Term.app
                       `Pi.single
                       [`i («term_-_» (Term.app `I.upper [`i]) "-" (Term.app `I.lower [`i]))])])
                    "-"
                    («term_-_»
                     (Term.app `f [(Term.app `i.insert_nth [(Term.app `I.upper [`i]) `x])])
                     "-"
                     (Term.app `f [(Term.app `i.insert_nth [(Term.app `I.lower [`i]) `x])])))))
                 `box_additive_map.volume])
               "‖"))
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
                      `integral_sub
                      [(Term.app `Hi [(Term.hole "_") `Hu]) (Term.app `Hi [(Term.hole "_") `Hl])]))
                    ","
                    (Tactic.rwRule
                     [(patternIgnore (token.«← » "←"))]
                     (Term.app `box.volume_face_mul [`i]))
                    ","
                    (Tactic.rwRule [] `mul_smul)
                    ","
                    (Tactic.rwRule [(patternIgnore (token.«← » "←"))] `box.volume_apply)
                    ","
                    (Tactic.rwRule
                     [(patternIgnore (token.«← » "←"))]
                     `box_additive_map.to_smul_apply)
                    ","
                    (Tactic.rwRule [(patternIgnore (token.«← » "←"))] `integral_const)
                    ","
                    (Tactic.rwRule [(patternIgnore (token.«← » "←"))] `box_additive_map.volume)
                    ","
                    (Tactic.rwRule
                     [(patternIgnore (token.«← » "←"))]
                     (Term.app
                      `integral_sub
                      [(Term.app `integrable_const [(Term.hole "_")])
                       (Term.app
                        (Term.proj (Term.app `Hi [(Term.hole "_") `Hu]) "." `sub)
                        [(Term.app `Hi [(Term.hole "_") `Hl])])]))]
                   "]")
                  [])
                 []
                 (Tactic.simp
                  "simp"
                  []
                  []
                  ["only"]
                  ["["
                   [(Tactic.simpLemma
                     []
                     []
                     (Term.paren "(" («term_∘_» (Term.cdot "·") "∘" (Term.cdot "·")) ")"))
                    ","
                    (Tactic.simpLemma [] [] `Pi.sub_def)
                    ","
                    (Tactic.simpLemma [] [(patternIgnore (token.«← » "←"))] `f'.map_smul)
                    ","
                    (Tactic.simpLemma [] [(patternIgnore (token.«← » "←"))] `Pi.single_smul')
                    ","
                    (Tactic.simpLemma [] [] `smul_eq_mul)
                    ","
                    (Tactic.simpLemma [] [] `mul_one)]
                   "]"]
                  [])]))))
            [(calcStep
              («term_≤_»
               (Term.hole "_")
               "≤"
               («term_*_»
                (Term.proj
                 (Term.app
                  `volume
                  [(Term.typeAscription
                    "("
                    (Term.app `I.face [`i])
                    ":"
                    [(Term.app
                      `Set
                      [(BoxIntegral.Analysis.BoxIntegral.DivergenceTheorem.«termℝⁿ» "ℝⁿ")])]
                    ")")])
                 "."
                 `toReal)
                "*"
                («term_*_»
                 («term_*_» («term_*_» (num "2") "*" `ε) "*" `c)
                 "*"
                 («term_-_» (Term.app `I.upper [`i]) "-" (Term.app `I.lower [`i])))))
              ":="
              (Term.byTactic
               "by"
               (Tactic.tacticSeq
                (Tactic.tacticSeq1Indented
                 [(Tactic.refine'
                   "refine'"
                   (Term.app
                    `norm_integral_le_of_le_const
                    [(Term.fun
                      "fun"
                      (Term.basicFun
                       [`y `hy]
                       []
                       "=>"
                       (Term.app
                        (Term.proj (Term.app `this [`y `hy]) "." `trans)
                        [(Term.hole "_")])))
                     `volume]))
                  []
                  (Tactic.rwSeq
                   "rw"
                   []
                   (Tactic.rwRuleSeq
                    "["
                    [(Tactic.rwRule [] (Term.app `mul_assoc [(«term_*_» (num "2") "*" `ε)]))]
                    "]")
                   [])
                  []
                  (Tactic.exact
                   "exact"
                   (Term.app
                    `mul_le_mul_of_nonneg_left
                    [(Term.app `I.diam_Icc_le_of_distortion_le [`i `hc])
                     (Term.app `mul_nonneg [`zero_le_two `h0.le])]))]))))
             (calcStep
              («term_=_»
               (Term.hole "_")
               "="
               («term_*_»
                («term_*_» («term_*_» (num "2") "*" `ε) "*" `c)
                "*"
                (BigOperators.Algebra.BigOperators.Basic.finset.prod_univ
                 "∏"
                 (Std.ExtendedBinder.extBinders
                  (Std.ExtendedBinder.extBinder (Lean.binderIdent `j) []))
                 ", "
                 («term_-_» (Term.app `I.upper [`j]) "-" (Term.app `I.lower [`j])))))
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
                      `measure.to_box_additive_apply)
                     ","
                     (Tactic.rwRule [] `box.volume_apply)
                     ","
                     (Tactic.rwRule
                      [(patternIgnore (token.«← » "←"))]
                      (Term.app `I.volume_face_mul [`i]))]
                    "]")
                   [])
                  []
                  (Tactic.acRfl "ac_rfl")]))))])])))
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
         [(Tactic.tacticHave_
           "have"
           (Term.haveDecl
            (Term.haveIdDecl
             [`Hl []]
             [(Term.typeSpec
               ":"
               («term_∈_»
                (Term.app `I.lower [`i])
                "∈"
                (Term.app `Icc [(Term.app `I.lower [`i]) (Term.app `I.upper [`i])])))]
             ":="
             (Term.app
              (Term.proj `Set.left_mem_Icc "." (fieldIdx "2"))
              [(Term.app `I.lower_le_upper [`i])]))))
          []
          (Tactic.tacticHave_
           "have"
           (Term.haveDecl
            (Term.haveIdDecl
             [`Hu []]
             [(Term.typeSpec
               ":"
               («term_∈_»
                (Term.app `I.upper [`i])
                "∈"
                (Term.app `Icc [(Term.app `I.lower [`i]) (Term.app `I.upper [`i])])))]
             ":="
             (Term.app
              (Term.proj `Set.right_mem_Icc "." (fieldIdx "2"))
              [(Term.app `I.lower_le_upper [`i])]))))
          []
          (Tactic.tacticHave_
           "have"
           (Term.haveDecl
            (Term.haveIdDecl
             [`Hi []]
             [(Term.typeSpec
               ":"
               (Std.ExtendedBinder.«term∀__,_»
                "∀"
                (Lean.binderIdent `x)
                («binderTerm∈_»
                 "∈"
                 (Term.app `Icc [(Term.app `I.lower [`i]) (Term.app `I.upper [`i])]))
                ","
                (Term.app
                 (Term.explicitUniv `Integrable ".{" [(num "0") "," `u "," `u] "}")
                 [(Term.app `I.face [`i])
                  (Order.BoundedOrder.«term⊥» "⊥")
                  («term_∘_» `f "∘" (Term.app `i.insert_nth [`x]))
                  `box_additive_map.volume])))]
             ":="
             (Term.fun
              "fun"
              (Term.basicFun
               [`x `hx]
               []
               "=>"
               (Term.app
                `integrable_of_continuous_on
                [(Term.hole "_") (Term.app `box.continuous_on_face_Icc [`hfc `hx]) `volume]))))))
          []
          (Tactic.tacticHave_
           "have"
           (Term.haveDecl
            (Term.haveIdDecl
             []
             [(Term.typeSpec
               ":"
               (Std.ExtendedBinder.«term∀__,_»
                "∀"
                (Lean.binderIdent `y)
                («binderTerm∈_» "∈" (Term.proj (Term.app `I.face [`i]) "." `IccCat))
                ","
                («term_≤_»
                 (Analysis.Normed.Group.Basic.«term‖_‖»
                  "‖"
                  («term_-_»
                   (Term.app
                    `f'
                    [(Term.app
                      `Pi.single
                      [`i («term_-_» (Term.app `I.upper [`i]) "-" (Term.app `I.lower [`i]))])])
                   "-"
                   («term_-_»
                    (Term.app `f [(Term.app `i.insert_nth [(Term.app `I.upper [`i]) `y])])
                    "-"
                    (Term.app `f [(Term.app `i.insert_nth [(Term.app `I.lower [`i]) `y])])))
                  "‖")
                 "≤"
                 («term_*_» («term_*_» (num "2") "*" `ε) "*" (Term.app `diam [`I.Icc])))))]
             ":="
             (Term.byTactic
              "by"
              (Tactic.tacticSeq
               (Tactic.tacticSeq1Indented
                [(Tactic.intro "intro" [`y `hy])
                 []
                 (Mathlib.Tactic.set
                  "set"
                  []
                  (Mathlib.Tactic.setArgsRest
                   `g
                   []
                   ":="
                   (Term.fun
                    "fun"
                    (Term.basicFun
                     [`y]
                     []
                     "=>"
                     («term_-_»
                      («term_-_» (Term.app `f [`y]) "-" `a)
                      "-"
                      (Term.app `f' [(«term_-_» `y "-" `x)]))))
                   ["with" [] `hg]))
                 []
                 (Tactic.change
                  "change"
                  (Std.ExtendedBinder.«term∀__,_»
                   "∀"
                   (Lean.binderIdent `y)
                   («binderTerm∈_» "∈" `I.Icc)
                   ","
                   («term_≤_»
                    (Analysis.Normed.Group.Basic.«term‖_‖» "‖" (Term.app `g [`y]) "‖")
                    "≤"
                    («term_*_»
                     `ε
                     "*"
                     (Analysis.Normed.Group.Basic.«term‖_‖» "‖" («term_-_» `y "-" `x) "‖"))))
                  [(Tactic.location "at" (Tactic.locationHyp [`hε] []))])
                 []
                 (Tactic.clearValue "clear_value" [(group `g)])
                 []
                 (Std.Tactic.obtain
                  "obtain"
                  [(Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `rfl)])]
                  [":"
                   («term_=_»
                    `f
                    "="
                    (Term.fun
                     "fun"
                     (Term.basicFun
                      [`y]
                      []
                      "=>"
                      («term_+_»
                       («term_+_» `a "+" (Term.app `f' [(«term_-_» `y "-" `x)]))
                       "+"
                       (Term.app `g [`y])))))]
                  [":="
                   [(Term.byTactic
                     "by"
                     (Tactic.tacticSeq
                      (Tactic.tacticSeq1Indented
                       [(Tactic.simp
                         "simp"
                         []
                         []
                         []
                         ["[" [(Tactic.simpLemma [] [] `hg)] "]"]
                         [])])))]])
                 []
                 (convertTo
                  "convert_to"
                  («term_≤_»
                   (Analysis.Normed.Group.Basic.«term‖_‖»
                    "‖"
                    («term_-_»
                     (Term.app `g [(Term.app `i.insert_nth [(Term.app `I.lower [`i]) `y])])
                     "-"
                     (Term.app `g [(Term.app `i.insert_nth [(Term.app `I.upper [`i]) `y])]))
                    "‖")
                   "≤"
                   (Term.hole "_"))
                  [])
                 []
                 (tactic__
                  (cdotTk (patternIgnore (token.«· » "·")))
                  [(Tactic.congr "congr" [(num "1")])
                   []
                   (Tactic.tacticHave_
                    "have"
                    (Term.haveDecl
                     (Term.haveIdDecl
                      []
                      []
                      ":="
                      (Term.app
                       `Fin.insert_nth_sub_same
                       [`i (Term.app `I.upper [`i]) (Term.app `I.lower [`i]) `y]))))
                   []
                   (Tactic.simp
                    "simp"
                    []
                    []
                    ["only"]
                    ["["
                     [(Tactic.simpLemma [] [(patternIgnore (token.«← » "←"))] `this)
                      ","
                      (Tactic.simpLemma [] [] `f'.map_sub)]
                     "]"]
                    [])
                   []
                   (Tactic.abel "abel" [] [])])
                 []
                 (tactic__
                  (cdotTk (patternIgnore (token.«· » "·")))
                  [(Tactic.tacticHave_
                    "have"
                    (Term.haveDecl
                     (Term.haveIdDecl
                      []
                      [(Term.typeSpec
                        ":"
                        (Std.ExtendedBinder.«term∀__,_»
                         "∀"
                         (Lean.binderIdent `z)
                         («binderTerm∈_»
                          "∈"
                          (Term.app `Icc [(Term.app `I.lower [`i]) (Term.app `I.upper [`i])]))
                         ","
                         («term_∈_» (Term.app `i.insert_nth [`z `y]) "∈" `I.Icc)))]
                      ":="
                      (Term.fun
                       "fun"
                       (Term.basicFun
                        [`z `hz]
                        []
                        "=>"
                        (Term.app `I.maps_to_insert_nth_face_Icc [`hz `hy]))))))
                   []
                   (Mathlib.Tactic.replace'
                    "replace"
                    [`hε []]
                    [(Term.typeSpec
                      ":"
                      (Std.ExtendedBinder.«term∀__,_»
                       "∀"
                       (Lean.binderIdent `y)
                       («binderTerm∈_» "∈" `I.Icc)
                       ","
                       («term_≤_»
                        (Analysis.Normed.Group.Basic.«term‖_‖» "‖" (Term.app `g [`y]) "‖")
                        "≤"
                        («term_*_» `ε "*" (Term.app `diam [`I.Icc])))))])
                   []
                   (tactic__
                    (cdotTk (patternIgnore (token.«· » "·")))
                    [(Tactic.intro "intro" [`y `hy])
                     []
                     (Tactic.refine'
                      "refine'"
                      (Term.app
                       (Term.proj (Term.app `hε [`y `hy]) "." `trans)
                       [(Term.app `mul_le_mul_of_nonneg_left [(Term.hole "_") `h0.le])]))
                     []
                     (Tactic.rwSeq
                      "rw"
                      []
                      (Tactic.rwRuleSeq
                       "["
                       [(Tactic.rwRule [(patternIgnore (token.«← » "←"))] `dist_eq_norm)]
                       "]")
                      [])
                     []
                     (Tactic.exact
                      "exact"
                      (Term.app `dist_le_diam_of_mem [`I.is_compact_Icc.bounded `hy `hxI]))])
                   []
                   (Tactic.rwSeq
                    "rw"
                    []
                    (Tactic.rwRuleSeq
                     "["
                     [(Tactic.rwRule [] `two_mul) "," (Tactic.rwRule [] `add_mul)]
                     "]")
                    [])
                   []
                   (Tactic.exact
                    "exact"
                    (Term.app
                     `norm_sub_le_of_le
                     [(Term.app `hε [(Term.hole "_") (Term.app `this [(Term.hole "_") `Hl])])
                      (Term.app
                       `hε
                       [(Term.hole "_") (Term.app `this [(Term.hole "_") `Hu])])]))])]))))))
          []
          (calcTactic
           "calc"
           (calcStep
            («term_=_»
             (Analysis.Normed.Group.Basic.«term‖_‖»
              "‖"
              («term_-_»
               (Algebra.Group.Defs.«term_•_»
                (BigOperators.Algebra.BigOperators.Basic.finset.prod_univ
                 "∏"
                 (Std.ExtendedBinder.extBinders
                  (Std.ExtendedBinder.extBinder (Lean.binderIdent `j) []))
                 ", "
                 («term_-_» (Term.app `I.upper [`j]) "-" (Term.app `I.lower [`j])))
                " • "
                (Term.app `f' [(Term.app `Pi.single [`i (num "1")])]))
               "-"
               («term_-_»
                (Term.app
                 `integral
                 [(Term.app `I.face [`i])
                  (Order.BoundedOrder.«term⊥» "⊥")
                  («term_∘_» `f "∘" (Term.app `i.insert_nth [(Term.app `I.upper [`i])]))
                  `box_additive_map.volume])
                "-"
                (Term.app
                 `integral
                 [(Term.app `I.face [`i])
                  (Order.BoundedOrder.«term⊥» "⊥")
                  («term_∘_» `f "∘" (Term.app `i.insert_nth [(Term.app `I.lower [`i])]))
                  `box_additive_map.volume])))
              "‖")
             "="
             (Analysis.Normed.Group.Basic.«term‖_‖»
              "‖"
              (Term.app
               (Term.explicitUniv `integral ".{" [(num "0") "," `u "," `u] "}")
               [(Term.app `I.face [`i])
                (Order.BoundedOrder.«term⊥» "⊥")
                (Term.fun
                 "fun"
                 (Term.basicFun
                  [`x]
                  [(Term.typeSpec
                    ":"
                    (Term.arrow (Term.app `Fin [`n]) "→" (Data.Real.Basic.termℝ "ℝ")))]
                  "=>"
                  («term_-_»
                   (Term.app
                    `f'
                    [(Term.app
                      `Pi.single
                      [`i («term_-_» (Term.app `I.upper [`i]) "-" (Term.app `I.lower [`i]))])])
                   "-"
                   («term_-_»
                    (Term.app `f [(Term.app `i.insert_nth [(Term.app `I.upper [`i]) `x])])
                    "-"
                    (Term.app `f [(Term.app `i.insert_nth [(Term.app `I.lower [`i]) `x])])))))
                `box_additive_map.volume])
              "‖"))
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
                     `integral_sub
                     [(Term.app `Hi [(Term.hole "_") `Hu]) (Term.app `Hi [(Term.hole "_") `Hl])]))
                   ","
                   (Tactic.rwRule
                    [(patternIgnore (token.«← » "←"))]
                    (Term.app `box.volume_face_mul [`i]))
                   ","
                   (Tactic.rwRule [] `mul_smul)
                   ","
                   (Tactic.rwRule [(patternIgnore (token.«← » "←"))] `box.volume_apply)
                   ","
                   (Tactic.rwRule
                    [(patternIgnore (token.«← » "←"))]
                    `box_additive_map.to_smul_apply)
                   ","
                   (Tactic.rwRule [(patternIgnore (token.«← » "←"))] `integral_const)
                   ","
                   (Tactic.rwRule [(patternIgnore (token.«← » "←"))] `box_additive_map.volume)
                   ","
                   (Tactic.rwRule
                    [(patternIgnore (token.«← » "←"))]
                    (Term.app
                     `integral_sub
                     [(Term.app `integrable_const [(Term.hole "_")])
                      (Term.app
                       (Term.proj (Term.app `Hi [(Term.hole "_") `Hu]) "." `sub)
                       [(Term.app `Hi [(Term.hole "_") `Hl])])]))]
                  "]")
                 [])
                []
                (Tactic.simp
                 "simp"
                 []
                 []
                 ["only"]
                 ["["
                  [(Tactic.simpLemma
                    []
                    []
                    (Term.paren "(" («term_∘_» (Term.cdot "·") "∘" (Term.cdot "·")) ")"))
                   ","
                   (Tactic.simpLemma [] [] `Pi.sub_def)
                   ","
                   (Tactic.simpLemma [] [(patternIgnore (token.«← » "←"))] `f'.map_smul)
                   ","
                   (Tactic.simpLemma [] [(patternIgnore (token.«← » "←"))] `Pi.single_smul')
                   ","
                   (Tactic.simpLemma [] [] `smul_eq_mul)
                   ","
                   (Tactic.simpLemma [] [] `mul_one)]
                  "]"]
                 [])]))))
           [(calcStep
             («term_≤_»
              (Term.hole "_")
              "≤"
              («term_*_»
               (Term.proj
                (Term.app
                 `volume
                 [(Term.typeAscription
                   "("
                   (Term.app `I.face [`i])
                   ":"
                   [(Term.app
                     `Set
                     [(BoxIntegral.Analysis.BoxIntegral.DivergenceTheorem.«termℝⁿ» "ℝⁿ")])]
                   ")")])
                "."
                `toReal)
               "*"
               («term_*_»
                («term_*_» («term_*_» (num "2") "*" `ε) "*" `c)
                "*"
                («term_-_» (Term.app `I.upper [`i]) "-" (Term.app `I.lower [`i])))))
             ":="
             (Term.byTactic
              "by"
              (Tactic.tacticSeq
               (Tactic.tacticSeq1Indented
                [(Tactic.refine'
                  "refine'"
                  (Term.app
                   `norm_integral_le_of_le_const
                   [(Term.fun
                     "fun"
                     (Term.basicFun
                      [`y `hy]
                      []
                      "=>"
                      (Term.app
                       (Term.proj (Term.app `this [`y `hy]) "." `trans)
                       [(Term.hole "_")])))
                    `volume]))
                 []
                 (Tactic.rwSeq
                  "rw"
                  []
                  (Tactic.rwRuleSeq
                   "["
                   [(Tactic.rwRule [] (Term.app `mul_assoc [(«term_*_» (num "2") "*" `ε)]))]
                   "]")
                  [])
                 []
                 (Tactic.exact
                  "exact"
                  (Term.app
                   `mul_le_mul_of_nonneg_left
                   [(Term.app `I.diam_Icc_le_of_distortion_le [`i `hc])
                    (Term.app `mul_nonneg [`zero_le_two `h0.le])]))]))))
            (calcStep
             («term_=_»
              (Term.hole "_")
              "="
              («term_*_»
               («term_*_» («term_*_» (num "2") "*" `ε) "*" `c)
               "*"
               (BigOperators.Algebra.BigOperators.Basic.finset.prod_univ
                "∏"
                (Std.ExtendedBinder.extBinders
                 (Std.ExtendedBinder.extBinder (Lean.binderIdent `j) []))
                ", "
                («term_-_» (Term.app `I.upper [`j]) "-" (Term.app `I.lower [`j])))))
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
                     `measure.to_box_additive_apply)
                    ","
                    (Tactic.rwRule [] `box.volume_apply)
                    ","
                    (Tactic.rwRule
                     [(patternIgnore (token.«← » "←"))]
                     (Term.app `I.volume_face_mul [`i]))]
                   "]")
                  [])
                 []
                 (Tactic.acRfl "ac_rfl")]))))])])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (calcTactic
       "calc"
       (calcStep
        («term_=_»
         (Analysis.Normed.Group.Basic.«term‖_‖»
          "‖"
          («term_-_»
           (Algebra.Group.Defs.«term_•_»
            (BigOperators.Algebra.BigOperators.Basic.finset.prod_univ
             "∏"
             (Std.ExtendedBinder.extBinders (Std.ExtendedBinder.extBinder (Lean.binderIdent `j) []))
             ", "
             («term_-_» (Term.app `I.upper [`j]) "-" (Term.app `I.lower [`j])))
            " • "
            (Term.app `f' [(Term.app `Pi.single [`i (num "1")])]))
           "-"
           («term_-_»
            (Term.app
             `integral
             [(Term.app `I.face [`i])
              (Order.BoundedOrder.«term⊥» "⊥")
              («term_∘_» `f "∘" (Term.app `i.insert_nth [(Term.app `I.upper [`i])]))
              `box_additive_map.volume])
            "-"
            (Term.app
             `integral
             [(Term.app `I.face [`i])
              (Order.BoundedOrder.«term⊥» "⊥")
              («term_∘_» `f "∘" (Term.app `i.insert_nth [(Term.app `I.lower [`i])]))
              `box_additive_map.volume])))
          "‖")
         "="
         (Analysis.Normed.Group.Basic.«term‖_‖»
          "‖"
          (Term.app
           (Term.explicitUniv `integral ".{" [(num "0") "," `u "," `u] "}")
           [(Term.app `I.face [`i])
            (Order.BoundedOrder.«term⊥» "⊥")
            (Term.fun
             "fun"
             (Term.basicFun
              [`x]
              [(Term.typeSpec
                ":"
                (Term.arrow (Term.app `Fin [`n]) "→" (Data.Real.Basic.termℝ "ℝ")))]
              "=>"
              («term_-_»
               (Term.app
                `f'
                [(Term.app
                  `Pi.single
                  [`i («term_-_» (Term.app `I.upper [`i]) "-" (Term.app `I.lower [`i]))])])
               "-"
               («term_-_»
                (Term.app `f [(Term.app `i.insert_nth [(Term.app `I.upper [`i]) `x])])
                "-"
                (Term.app `f [(Term.app `i.insert_nth [(Term.app `I.lower [`i]) `x])])))))
            `box_additive_map.volume])
          "‖"))
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
                 `integral_sub
                 [(Term.app `Hi [(Term.hole "_") `Hu]) (Term.app `Hi [(Term.hole "_") `Hl])]))
               ","
               (Tactic.rwRule
                [(patternIgnore (token.«← » "←"))]
                (Term.app `box.volume_face_mul [`i]))
               ","
               (Tactic.rwRule [] `mul_smul)
               ","
               (Tactic.rwRule [(patternIgnore (token.«← » "←"))] `box.volume_apply)
               ","
               (Tactic.rwRule [(patternIgnore (token.«← » "←"))] `box_additive_map.to_smul_apply)
               ","
               (Tactic.rwRule [(patternIgnore (token.«← » "←"))] `integral_const)
               ","
               (Tactic.rwRule [(patternIgnore (token.«← » "←"))] `box_additive_map.volume)
               ","
               (Tactic.rwRule
                [(patternIgnore (token.«← » "←"))]
                (Term.app
                 `integral_sub
                 [(Term.app `integrable_const [(Term.hole "_")])
                  (Term.app
                   (Term.proj (Term.app `Hi [(Term.hole "_") `Hu]) "." `sub)
                   [(Term.app `Hi [(Term.hole "_") `Hl])])]))]
              "]")
             [])
            []
            (Tactic.simp
             "simp"
             []
             []
             ["only"]
             ["["
              [(Tactic.simpLemma
                []
                []
                (Term.paren "(" («term_∘_» (Term.cdot "·") "∘" (Term.cdot "·")) ")"))
               ","
               (Tactic.simpLemma [] [] `Pi.sub_def)
               ","
               (Tactic.simpLemma [] [(patternIgnore (token.«← » "←"))] `f'.map_smul)
               ","
               (Tactic.simpLemma [] [(patternIgnore (token.«← » "←"))] `Pi.single_smul')
               ","
               (Tactic.simpLemma [] [] `smul_eq_mul)
               ","
               (Tactic.simpLemma [] [] `mul_one)]
              "]"]
             [])]))))
       [(calcStep
         («term_≤_»
          (Term.hole "_")
          "≤"
          («term_*_»
           (Term.proj
            (Term.app
             `volume
             [(Term.typeAscription
               "("
               (Term.app `I.face [`i])
               ":"
               [(Term.app
                 `Set
                 [(BoxIntegral.Analysis.BoxIntegral.DivergenceTheorem.«termℝⁿ» "ℝⁿ")])]
               ")")])
            "."
            `toReal)
           "*"
           («term_*_»
            («term_*_» («term_*_» (num "2") "*" `ε) "*" `c)
            "*"
            («term_-_» (Term.app `I.upper [`i]) "-" (Term.app `I.lower [`i])))))
         ":="
         (Term.byTactic
          "by"
          (Tactic.tacticSeq
           (Tactic.tacticSeq1Indented
            [(Tactic.refine'
              "refine'"
              (Term.app
               `norm_integral_le_of_le_const
               [(Term.fun
                 "fun"
                 (Term.basicFun
                  [`y `hy]
                  []
                  "=>"
                  (Term.app (Term.proj (Term.app `this [`y `hy]) "." `trans) [(Term.hole "_")])))
                `volume]))
             []
             (Tactic.rwSeq
              "rw"
              []
              (Tactic.rwRuleSeq
               "["
               [(Tactic.rwRule [] (Term.app `mul_assoc [(«term_*_» (num "2") "*" `ε)]))]
               "]")
              [])
             []
             (Tactic.exact
              "exact"
              (Term.app
               `mul_le_mul_of_nonneg_left
               [(Term.app `I.diam_Icc_le_of_distortion_le [`i `hc])
                (Term.app `mul_nonneg [`zero_le_two `h0.le])]))]))))
        (calcStep
         («term_=_»
          (Term.hole "_")
          "="
          («term_*_»
           («term_*_» («term_*_» (num "2") "*" `ε) "*" `c)
           "*"
           (BigOperators.Algebra.BigOperators.Basic.finset.prod_univ
            "∏"
            (Std.ExtendedBinder.extBinders (Std.ExtendedBinder.extBinder (Lean.binderIdent `j) []))
            ", "
            («term_-_» (Term.app `I.upper [`j]) "-" (Term.app `I.lower [`j])))))
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
               [(Tactic.rwRule [(patternIgnore (token.«← » "←"))] `measure.to_box_additive_apply)
                ","
                (Tactic.rwRule [] `box.volume_apply)
                ","
                (Tactic.rwRule
                 [(patternIgnore (token.«← » "←"))]
                 (Term.app `I.volume_face_mul [`i]))]
               "]")
              [])
             []
             (Tactic.acRfl "ac_rfl")]))))])
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
            [(Tactic.rwRule [(patternIgnore (token.«← » "←"))] `measure.to_box_additive_apply)
             ","
             (Tactic.rwRule [] `box.volume_apply)
             ","
             (Tactic.rwRule [(patternIgnore (token.«← » "←"))] (Term.app `I.volume_face_mul [`i]))]
            "]")
           [])
          []
          (Tactic.acRfl "ac_rfl")])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.acRfl "ac_rfl")
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.rwSeq
       "rw"
       []
       (Tactic.rwRuleSeq
        "["
        [(Tactic.rwRule [(patternIgnore (token.«← » "←"))] `measure.to_box_additive_apply)
         ","
         (Tactic.rwRule [] `box.volume_apply)
         ","
         (Tactic.rwRule [(patternIgnore (token.«← » "←"))] (Term.app `I.volume_face_mul [`i]))]
        "]")
       [])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `I.volume_face_mul [`i])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `i
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `I.volume_face_mul
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `box.volume_apply
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `measure.to_box_additive_apply
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, tactic) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_=_»
       (Term.hole "_")
       "="
       («term_*_»
        («term_*_» («term_*_» (num "2") "*" `ε) "*" `c)
        "*"
        (BigOperators.Algebra.BigOperators.Basic.finset.prod_univ
         "∏"
         (Std.ExtendedBinder.extBinders (Std.ExtendedBinder.extBinder (Lean.binderIdent `j) []))
         ", "
         («term_-_» (Term.app `I.upper [`j]) "-" (Term.app `I.lower [`j])))))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_*_»
       («term_*_» («term_*_» (num "2") "*" `ε) "*" `c)
       "*"
       (BigOperators.Algebra.BigOperators.Basic.finset.prod_univ
        "∏"
        (Std.ExtendedBinder.extBinders (Std.ExtendedBinder.extBinder (Lean.binderIdent `j) []))
        ", "
        («term_-_» (Term.app `I.upper [`j]) "-" (Term.app `I.lower [`j]))))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (BigOperators.Algebra.BigOperators.Basic.finset.prod_univ
       "∏"
       (Std.ExtendedBinder.extBinders (Std.ExtendedBinder.extBinder (Lean.binderIdent `j) []))
       ", "
       («term_-_» (Term.app `I.upper [`j]) "-" (Term.app `I.lower [`j])))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_-_» (Term.app `I.upper [`j]) "-" (Term.app `I.lower [`j]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `I.lower [`j])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `j
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `I.lower
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 66 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 65, term))
      (Term.app `I.upper [`j])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `j
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `I.upper
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 65 >? 1022, (some 1023, term) <=? (some 65, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 65, (some 66, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 71 >? 1022, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 70, term))
      («term_*_» («term_*_» (num "2") "*" `ε) "*" `c)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `c
[PrettyPrinter.parenthesize] ...precedences are 71 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 70, term))
      («term_*_» (num "2") "*" `ε)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `ε
[PrettyPrinter.parenthesize] ...precedences are 71 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 70, term))
      (num "2")
[PrettyPrinter.parenthesize] ...precedences are 70 >? 1024, (none, [anonymous]) <=? (some 70, term)
[PrettyPrinter.parenthesize] ...precedences are 70 >? 70, (some 71, term) <=? (some 70, term)
[PrettyPrinter.parenthesize] ...precedences are 70 >? 70, (some 71, term) <=? (some 70, term)
[PrettyPrinter.parenthesize] ...precedences are 51 >? 70, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 50, term))
      (Term.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1024, (none, [anonymous]) <=? (some 50, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 50, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, term))
      (Term.byTactic
       "by"
       (Tactic.tacticSeq
        (Tactic.tacticSeq1Indented
         [(Tactic.refine'
           "refine'"
           (Term.app
            `norm_integral_le_of_le_const
            [(Term.fun
              "fun"
              (Term.basicFun
               [`y `hy]
               []
               "=>"
               (Term.app (Term.proj (Term.app `this [`y `hy]) "." `trans) [(Term.hole "_")])))
             `volume]))
          []
          (Tactic.rwSeq
           "rw"
           []
           (Tactic.rwRuleSeq
            "["
            [(Tactic.rwRule [] (Term.app `mul_assoc [(«term_*_» (num "2") "*" `ε)]))]
            "]")
           [])
          []
          (Tactic.exact
           "exact"
           (Term.app
            `mul_le_mul_of_nonneg_left
            [(Term.app `I.diam_Icc_le_of_distortion_le [`i `hc])
             (Term.app `mul_nonneg [`zero_le_two `h0.le])]))])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.exact
       "exact"
       (Term.app
        `mul_le_mul_of_nonneg_left
        [(Term.app `I.diam_Icc_le_of_distortion_le [`i `hc])
         (Term.app `mul_nonneg [`zero_le_two `h0.le])]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       `mul_le_mul_of_nonneg_left
       [(Term.app `I.diam_Icc_le_of_distortion_le [`i `hc])
        (Term.app `mul_nonneg [`zero_le_two `h0.le])])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `mul_nonneg [`zero_le_two `h0.le])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `h0.le
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `zero_le_two
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `mul_nonneg
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.app `mul_nonneg [`zero_le_two `h0.le])
     ")")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.app `I.diam_Icc_le_of_distortion_le [`i `hc])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `hc
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `i
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `I.diam_Icc_le_of_distortion_le
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023,
     term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.app `I.diam_Icc_le_of_distortion_le [`i `hc])
     ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `mul_le_mul_of_nonneg_left
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
        [(Tactic.rwRule [] (Term.app `mul_assoc [(«term_*_» (num "2") "*" `ε)]))]
        "]")
       [])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `mul_assoc [(«term_*_» (num "2") "*" `ε)])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_*_»', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_*_»', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_*_» (num "2") "*" `ε)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `ε
[PrettyPrinter.parenthesize] ...precedences are 71 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 70, term))
      (num "2")
[PrettyPrinter.parenthesize] ...precedences are 70 >? 1024, (none, [anonymous]) <=? (some 70, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 70, (some 71, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren "(" («term_*_» (num "2") "*" `ε) ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `mul_assoc
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.refine'
       "refine'"
       (Term.app
        `norm_integral_le_of_le_const
        [(Term.fun
          "fun"
          (Term.basicFun
           [`y `hy]
           []
           "=>"
           (Term.app (Term.proj (Term.app `this [`y `hy]) "." `trans) [(Term.hole "_")])))
         `volume]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       `norm_integral_le_of_le_const
       [(Term.fun
         "fun"
         (Term.basicFun
          [`y `hy]
          []
          "=>"
          (Term.app (Term.proj (Term.app `this [`y `hy]) "." `trans) [(Term.hole "_")])))
        `volume])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `volume
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.fun
       "fun"
       (Term.basicFun
        [`y `hy]
        []
        "=>"
        (Term.app (Term.proj (Term.app `this [`y `hy]) "." `trans) [(Term.hole "_")])))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app (Term.proj (Term.app `this [`y `hy]) "." `trans) [(Term.hole "_")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (Term.proj (Term.app `this [`y `hy]) "." `trans)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.app `this [`y `hy])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `hy
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `y
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `this
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren "(" (Term.app `this [`y `hy]) ")")
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.strictImplicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.implicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.instBinder'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `hy
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.strictImplicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.implicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.instBinder'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `y
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (some 0, term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.fun
      "fun"
      (Term.basicFun
       [`y `hy]
       []
       "=>"
       (Term.app
        (Term.proj (Term.paren "(" (Term.app `this [`y `hy]) ")") "." `trans)
        [(Term.hole "_")])))
     ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `norm_integral_le_of_le_const
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, tactic) <=? (none, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_≤_»
       (Term.hole "_")
       "≤"
       («term_*_»
        (Term.proj
         (Term.app
          `volume
          [(Term.typeAscription
            "("
            (Term.app `I.face [`i])
            ":"
            [(Term.app `Set [(BoxIntegral.Analysis.BoxIntegral.DivergenceTheorem.«termℝⁿ» "ℝⁿ")])]
            ")")])
         "."
         `toReal)
        "*"
        («term_*_»
         («term_*_» («term_*_» (num "2") "*" `ε) "*" `c)
         "*"
         («term_-_» (Term.app `I.upper [`i]) "-" (Term.app `I.lower [`i])))))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_*_»
       (Term.proj
        (Term.app
         `volume
         [(Term.typeAscription
           "("
           (Term.app `I.face [`i])
           ":"
           [(Term.app `Set [(BoxIntegral.Analysis.BoxIntegral.DivergenceTheorem.«termℝⁿ» "ℝⁿ")])]
           ")")])
        "."
        `toReal)
       "*"
       («term_*_»
        («term_*_» («term_*_» (num "2") "*" `ε) "*" `c)
        "*"
        («term_-_» (Term.app `I.upper [`i]) "-" (Term.app `I.lower [`i]))))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_*_»
       («term_*_» («term_*_» (num "2") "*" `ε) "*" `c)
       "*"
       («term_-_» (Term.app `I.upper [`i]) "-" (Term.app `I.lower [`i])))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_-_» (Term.app `I.upper [`i]) "-" (Term.app `I.lower [`i]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `I.lower [`i])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `i
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `I.lower
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 66 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 65, term))
      (Term.app `I.upper [`i])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `i
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `I.upper
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 65 >? 1022, (some 1023, term) <=? (some 65, term)
[PrettyPrinter.parenthesize] ...precedences are 71 >? 65, (some 66, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     («term_-_» (Term.app `I.upper [`i]) "-" (Term.app `I.lower [`i]))
     ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 70, term))
      («term_*_» («term_*_» (num "2") "*" `ε) "*" `c)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `c
[PrettyPrinter.parenthesize] ...precedences are 71 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 70, term))
      («term_*_» (num "2") "*" `ε)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `ε
[PrettyPrinter.parenthesize] ...precedences are 71 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 70, term))
      (num "2")
[PrettyPrinter.parenthesize] ...precedences are 70 >? 1024, (none, [anonymous]) <=? (some 70, term)
[PrettyPrinter.parenthesize] ...precedences are 70 >? 70, (some 71, term) <=? (some 70, term)
[PrettyPrinter.parenthesize] ...precedences are 70 >? 70, (some 71, term) <=? (some 70, term)
[PrettyPrinter.parenthesize] ...precedences are 71 >? 70, (some 71, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     («term_*_»
      («term_*_» («term_*_» (num "2") "*" `ε) "*" `c)
      "*"
      (Term.paren "(" («term_-_» (Term.app `I.upper [`i]) "-" (Term.app `I.lower [`i])) ")"))
     ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 70, term))
      (Term.proj
       (Term.app
        `volume
        [(Term.typeAscription
          "("
          (Term.app `I.face [`i])
          ":"
          [(Term.app `Set [(BoxIntegral.Analysis.BoxIntegral.DivergenceTheorem.«termℝⁿ» "ℝⁿ")])]
          ")")])
       "."
       `toReal)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.app
       `volume
       [(Term.typeAscription
         "("
         (Term.app `I.face [`i])
         ":"
         [(Term.app `Set [(BoxIntegral.Analysis.BoxIntegral.DivergenceTheorem.«termℝⁿ» "ℝⁿ")])]
         ")")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.typeAscription', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.typeAscription', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.typeAscription
       "("
       (Term.app `I.face [`i])
       ":"
       [(Term.app `Set [(BoxIntegral.Analysis.BoxIntegral.DivergenceTheorem.«termℝⁿ» "ℝⁿ")])]
       ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `Set [(BoxIntegral.Analysis.BoxIntegral.DivergenceTheorem.«termℝⁿ» "ℝⁿ")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'BoxIntegral.Analysis.BoxIntegral.DivergenceTheorem.«termℝⁿ»', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'BoxIntegral.Analysis.BoxIntegral.DivergenceTheorem.«termℝⁿ»', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (BoxIntegral.Analysis.BoxIntegral.DivergenceTheorem.«termℝⁿ» "ℝⁿ")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'BoxIntegral.Analysis.BoxIntegral.DivergenceTheorem.«termℝⁿ»', expected 'BoxIntegral.Analysis.BoxIntegral.DivergenceTheorem.termℝⁿ._@.Analysis.BoxIntegral.DivergenceTheorem._hyg.9'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.declValSimple', expected 'Lean.Parser.Command.declValEqns'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.declValSimple', expected 'Lean.Parser.Command.whereStructInst'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.opaque'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.instance'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.axiom'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.example'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.inductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.classInductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.structure'-/-- failed to format: format: uncaught backtrack exception
/-- Auxiliary lemma for the divergence theorem. -/
  theorem
    norm_volume_sub_integral_face_upper_sub_lower_smul_le
    { f : ℝⁿ⁺¹ → E }
        { f' : ℝⁿ⁺¹ →L[ ℝ ] E }
        ( hfc : ContinuousOn f I . IccCat )
        { x : ℝⁿ⁺¹ }
        ( hxI : x ∈ I . IccCat )
        { a : E }
        { ε : ℝ }
        ( h0 : 0 < ε )
        ( hε : ∀ y ∈ I . IccCat , ‖ f y - a - f' y - x ‖ ≤ ε * ‖ y - x ‖ )
        { c : ℝ≥0 }
        ( hc : I . distortion ≤ c )
      :
        ‖
            ∏ j , I . upper j - I . lower j • f' Pi.single i 1
              -
              integral I . face i ⊥ f ∘ i . insertNth I . upper i BoxAdditiveMap.volume
                -
                integral I . face i ⊥ f ∘ i . insertNth I . lower i BoxAdditiveMap.volume
            ‖
          ≤
          2 * ε * c * ∏ j , I . upper j - I . lower j
    :=
      by
        have Hl : I.lower i ∈ Icc I.lower i I.upper i := Set.left_mem_Icc . 2 I.lower_le_upper i
          have Hu : I.upper i ∈ Icc I.lower i I.upper i := Set.right_mem_Icc . 2 I.lower_le_upper i
          have
            Hi
              :
                ∀
                  x
                  ∈ Icc I.lower i I.upper i
                  ,
                  Integrable .{ 0 , u , u } I.face i ⊥ f ∘ i.insert_nth x box_additive_map.volume
              :=
              fun x hx => integrable_of_continuous_on _ box.continuous_on_face_Icc hfc hx volume
          have
            :
                ∀
                  y
                  ∈ I.face i . IccCat
                  ,
                  ‖
                      f' Pi.single i I.upper i - I.lower i
                        -
                        f i.insert_nth I.upper i y - f i.insert_nth I.lower i y
                      ‖
                    ≤
                    2 * ε * diam I.Icc
              :=
              by
                intro y hy
                  set g := fun y => f y - a - f' y - x with hg
                  change ∀ y ∈ I.Icc , ‖ g y ‖ ≤ ε * ‖ y - x ‖ at hε
                  clear_value g
                  obtain rfl : f = fun y => a + f' y - x + g y := by simp [ hg ]
                  convert_to ‖ g i.insert_nth I.lower i y - g i.insert_nth I.upper i y ‖ ≤ _
                  ·
                    congr 1
                      have := Fin.insert_nth_sub_same i I.upper i I.lower i y
                      simp only [ ← this , f'.map_sub ]
                      abel
                  ·
                    have
                        : ∀ z ∈ Icc I.lower i I.upper i , i.insert_nth z y ∈ I.Icc
                          :=
                          fun z hz => I.maps_to_insert_nth_face_Icc hz hy
                      replace hε : ∀ y ∈ I.Icc , ‖ g y ‖ ≤ ε * diam I.Icc
                      ·
                        intro y hy
                          refine' hε y hy . trans mul_le_mul_of_nonneg_left _ h0.le
                          rw [ ← dist_eq_norm ]
                          exact dist_le_diam_of_mem I.is_compact_Icc.bounded hy hxI
                      rw [ two_mul , add_mul ]
                      exact norm_sub_le_of_le hε _ this _ Hl hε _ this _ Hu
          calc
            ‖
                  ∏ j , I.upper j - I.lower j • f' Pi.single i 1
                    -
                    integral I.face i ⊥ f ∘ i.insert_nth I.upper i box_additive_map.volume
                      -
                      integral I.face i ⊥ f ∘ i.insert_nth I.lower i box_additive_map.volume
                  ‖
                =
                ‖
                  integral .{ 0 , u , u }
                    I.face i
                      ⊥
                      fun
                        x
                          : Fin n → ℝ
                          =>
                          f' Pi.single i I.upper i - I.lower i
                            -
                            f i.insert_nth I.upper i x - f i.insert_nth I.lower i x
                      box_additive_map.volume
                  ‖
              :=
              by
                rw
                    [
                      ← integral_sub Hi _ Hu Hi _ Hl
                        ,
                        ← box.volume_face_mul i
                        ,
                        mul_smul
                        ,
                        ← box.volume_apply
                        ,
                        ← box_additive_map.to_smul_apply
                        ,
                        ← integral_const
                        ,
                        ← box_additive_map.volume
                        ,
                        ← integral_sub integrable_const _ Hi _ Hu . sub Hi _ Hl
                      ]
                  simp
                    only
                    [
                      ( · ∘ · )
                        ,
                        Pi.sub_def
                        ,
                        ← f'.map_smul
                        ,
                        ← Pi.single_smul'
                        ,
                        smul_eq_mul
                        ,
                        mul_one
                      ]
            _ ≤ volume ( I.face i : Set ℝⁿ ) . toReal * 2 * ε * c * I.upper i - I.lower i
                :=
                by
                  refine' norm_integral_le_of_le_const fun y hy => this y hy . trans _ volume
                    rw [ mul_assoc 2 * ε ]
                    exact
                      mul_le_mul_of_nonneg_left
                        I.diam_Icc_le_of_distortion_le i hc mul_nonneg zero_le_two h0.le
              _ = 2 * ε * c * ∏ j , I.upper j - I.lower j
                :=
                by
                  rw [ ← measure.to_box_additive_apply , box.volume_apply , ← I.volume_face_mul i ]
                    ac_rfl
#align
  box_integral.norm_volume_sub_integral_face_upper_sub_lower_smul_le BoxIntegral.norm_volume_sub_integral_face_upper_sub_lower_smul_le

/- ./././Mathport/Syntax/Translate/Basic.lean:632:2: warning: expanding binder collection (y₁ y₂ «expr ∈ » «expr ∩ »(closed_ball x δ, I.Icc)) -/
/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers
      [(Command.docComment
        "/--"
        "If `f : ℝⁿ⁺¹ → E` is differentiable on a closed rectangular box `I` with derivative `f'`, then\nthe partial derivative `λ x, f' x (pi.single i 1)` is Henstock-Kurzweil integrable with integral\nequal to the difference of integrals of `f` over the faces `x i = I.upper i` and `x i = I.lower i`.\n\nMore precisely, we use a non-standard generalization of the Henstock-Kurzweil integral and\nwe allow `f` to be non-differentiable (but still continuous) at a countable set of points.\n\nTODO: If `n > 0`, then the condition at `x ∈ s` can be replaced by a much weaker estimate but this\nrequires either better integrability theorems, or usage of a filter depending on the countable set\n`s` (we need to ensure that none of the faces of a partition contain a point from `s`). -/")]
      []
      []
      []
      []
      [])
     (Command.theorem
      "theorem"
      (Command.declId `hasIntegralGPPderiv [])
      (Command.declSig
       [(Term.explicitBinder
         "("
         [`f]
         [":"
          (Term.arrow
           (BoxIntegral.Analysis.BoxIntegral.DivergenceTheorem.«termℝⁿ⁺¹» "ℝⁿ⁺¹")
           "→"
           `E)]
         []
         ")")
        (Term.explicitBinder
         "("
         [`f']
         [":"
          (Term.arrow
           (BoxIntegral.Analysis.BoxIntegral.DivergenceTheorem.«termℝⁿ⁺¹» "ℝⁿ⁺¹")
           "→"
           (Topology.Algebra.Module.Basic.«term_→L[_]_»
            (BoxIntegral.Analysis.BoxIntegral.DivergenceTheorem.«termℝⁿ⁺¹» "ℝⁿ⁺¹")
            " →L["
            (Data.Real.Basic.termℝ "ℝ")
            "] "
            `E))]
         []
         ")")
        (Term.explicitBinder
         "("
         [`s]
         [":"
          (Term.app `Set [(BoxIntegral.Analysis.BoxIntegral.DivergenceTheorem.«termℝⁿ⁺¹» "ℝⁿ⁺¹")])]
         []
         ")")
        (Term.explicitBinder "(" [`hs] [":" (Term.proj `s "." `Countable)] [] ")")
        (Term.explicitBinder
         "("
         [`Hs]
         [":"
          (Std.ExtendedBinder.«term∀__,_»
           "∀"
           (Lean.binderIdent `x)
           («binderTerm∈_» "∈" `s)
           ","
           (Term.app `ContinuousWithinAt [`f (Term.proj `I "." `IccCat) `x]))]
         []
         ")")
        (Term.explicitBinder
         "("
         [`Hd]
         [":"
          (Std.ExtendedBinder.«term∀__,_»
           "∀"
           (Lean.binderIdent `x)
           («binderTerm∈_» "∈" («term_\_» (Term.proj `I "." `IccCat) "\\" `s))
           ","
           (Term.app `HasFderivWithinAt [`f (Term.app `f' [`x]) (Term.proj `I "." `IccCat) `x]))]
         []
         ")")
        (Term.explicitBinder "(" [`i] [":" (Term.app `Fin [(«term_+_» `n "+" (num "1"))])] [] ")")]
       (Term.typeSpec
        ":"
        (Term.app
         (Term.explicitUniv `HasIntegral ".{" [(num "0") "," `u "," `u] "}")
         [`I
          `gP
          (Term.fun
           "fun"
           (Term.basicFun [`x] [] "=>" (Term.app `f' [`x (Term.app `Pi.single [`i (num "1")])])))
          `BoxAdditiveMap.volume
          («term_-_»
           (Term.app
            (Term.explicitUniv `integral ".{" [(num "0") "," `u "," `u] "}")
            [(Term.app (Term.proj `I "." `face) [`i])
             `gP
             (Term.fun
              "fun"
              (Term.basicFun
               [`x]
               []
               "=>"
               (Term.app
                `f
                [(Term.app
                  (Term.proj `i "." `insertNth)
                  [(Term.app (Term.proj `I "." `upper) [`i]) `x])])))
             `BoxAdditiveMap.volume])
           "-"
           (Term.app
            (Term.explicitUniv `integral ".{" [(num "0") "," `u "," `u] "}")
            [(Term.app (Term.proj `I "." `face) [`i])
             `gP
             (Term.fun
              "fun"
              (Term.basicFun
               [`x]
               []
               "=>"
               (Term.app
                `f
                [(Term.app
                  (Term.proj `i "." `insertNth)
                  [(Term.app (Term.proj `I "." `lower) [`i]) `x])])))
             `BoxAdditiveMap.volume]))])))
      (Command.declValSimple
       ":="
       (Term.byTactic
        "by"
        (Tactic.tacticSeq
         (Tactic.tacticSeq1Indented
          [(Tactic.tacticHave_
            "have"
            (Term.haveDecl
             (Term.haveIdDecl
              [`Hc []]
              [(Term.typeSpec ":" (Term.app `ContinuousOn [`f `I.Icc]))]
              ":="
              (Term.byTactic
               "by"
               (Tactic.tacticSeq
                (Tactic.tacticSeq1Indented
                 [(Tactic.intro "intro" [`x `hx])
                  []
                  (Classical.«tacticBy_cases_:_» "by_cases" [`hxs ":"] («term_∈_» `x "∈" `s))
                  []
                  (Std.Tactic.exacts
                   "exacts"
                   "["
                   [(Term.app `Hs [`x `hxs])
                    ","
                    (Term.proj
                     (Term.app `Hd [`x (Term.anonymousCtor "⟨" [`hx "," `hxs] "⟩")])
                     "."
                     `ContinuousWithinAt)]
                   "]")]))))))
           []
           (Mathlib.Tactic.set
            "set"
            []
            (Mathlib.Tactic.setArgsRest
             `fI
             [":"
              (Term.arrow
               (Data.Real.Basic.termℝ "ℝ")
               "→"
               (Term.arrow (Term.app `box [(Term.app `Fin [`n])]) "→" `E))]
             ":="
             (Term.fun
              "fun"
              (Term.basicFun
               [`y `J]
               []
               "=>"
               (Term.app
                (Term.explicitUniv `integral ".{" [(num "0") "," `u "," `u] "}")
                [`J
                 `GP
                 (Term.fun
                  "fun"
                  (Term.basicFun [`x] [] "=>" (Term.app `f [(Term.app `i.insert_nth [`y `x])])))
                 `box_additive_map.volume])))
             []))
           []
           (Mathlib.Tactic.set
            "set"
            []
            (Mathlib.Tactic.setArgsRest
             `fb
             [":"
              (Term.arrow
               (Term.app `Icc [(Term.app `I.lower [`i]) (Term.app `I.upper [`i])])
               "→"
               (BoxIntegral.Analysis.BoxIntegral.Partition.Additive.box_integral.box_additive_map
                (Term.app `Fin [`n])
                " →ᵇᵃ["
                (coeNotation "↑" (Term.app `I.face [`i]))
                "] "
                `E))]
             ":="
             (Term.fun
              "fun"
              (Term.basicFun
               [`x]
               []
               "=>"
               (Term.proj
                (Term.app
                 `integrable_of_continuous_on
                 [`GP
                  (Term.app `box.continuous_on_face_Icc [`Hc (Term.proj `x "." (fieldIdx "2"))])
                  `volume])
                "."
                `toBoxAdditive)))
             []))
           []
           (Mathlib.Tactic.set
            "set"
            []
            (Mathlib.Tactic.setArgsRest
             `F
             [":"
              (BoxIntegral.Analysis.BoxIntegral.Partition.Additive.box_integral.box_additive_map
               (Term.app `Fin [(«term_+_» `n "+" (num "1"))])
               " →ᵇᵃ["
               `I
               "] "
               `E)]
             ":="
             (Term.app
              `box_additive_map.upper_sub_lower
              [`I `i `fI `fb (Term.fun "fun" (Term.basicFun [`x `hx `J] [] "=>" `rfl))])
             []))
           []
           (Tactic.change
            "change"
            (Term.app
             `has_integral
             [`I
              `GP
              (Term.fun
               "fun"
               (Term.basicFun
                [`x]
                []
                "=>"
                (Term.app `f' [`x (Term.app `Pi.single [`i (num "1")])])))
              (Term.hole "_")
              (Term.app `F [`I])])
            [])
           []
           (Tactic.refine'
            "refine'"
            (Term.app
             `has_integral_of_le_Henstock_of_forall_is_o
             [`GP_le
              (Term.hole "_")
              (Term.hole "_")
              (Term.hole "_")
              `s
              `hs
              (Term.hole "_")
              (Term.hole "_")]))
           []
           (tactic__
            (cdotTk (patternIgnore (token.«· » "·")))
            [(Tactic.exact
              "exact"
              (Term.app
               (Term.proj
                (Term.proj
                 (Term.typeAscription
                  "("
                  `volume
                  ":"
                  [(Term.app
                    `Measure
                    [(BoxIntegral.Analysis.BoxIntegral.DivergenceTheorem.«termℝⁿ⁺¹» "ℝⁿ⁺¹")])]
                  ")")
                 "."
                 `toBoxAdditive)
                "."
                `restrict)
               [(Term.hole "_") `le_top]))])
           []
           (tactic__
            (cdotTk (patternIgnore (token.«· » "·")))
            [(Tactic.exact
              "exact"
              (Term.fun "fun" (Term.basicFun [`J] [] "=>" `Ennreal.to_real_nonneg)))])
           []
           (tactic__
            (cdotTk (patternIgnore (token.«· » "·")))
            [(Tactic.intro "intro" [`c `x `hx `ε `ε0])
             []
             (Tactic.tacticHave_
              "have"
              (Term.haveDecl
               (Term.haveIdDecl
                []
                [(Term.typeSpec
                  ":"
                  (Filter.Order.Filter.Basic.«term∀ᶠ_in_,_»
                   "∀ᶠ"
                   (Std.ExtendedBinder.extBinders
                    (Std.ExtendedBinder.extBinder (Lean.binderIdent `δ) []))
                   " in "
                   (TopologicalSpace.Topology.Basic.nhds_within.gt
                    "𝓝[>] "
                    (Term.typeAscription "(" (num "0") ":" [(Data.Real.Basic.termℝ "ℝ")] ")"))
                   ", "
                   («term_∧_»
                    («term_∈_»
                     `δ
                     "∈"
                     (Term.app
                      `Ioc
                      [(Term.typeAscription "(" (num "0") ":" [(Data.Real.Basic.termℝ "ℝ")] ")")
                       («term_/_» (num "1") "/" (num "2"))]))
                    "∧"
                    («term_∧_»
                     (Term.forall
                      "∀"
                      [(Term.explicitBinder "(" [`y₁] [] [] ")")
                       (Term.explicitBinder
                        "("
                        [(Term.hole "_")]
                        [":"
                         («term_∈_» `y₁ "∈" («term_∩_» (Term.app `closed_ball [`x `δ]) "∩" `I.Icc))]
                        []
                        ")")
                       (Term.explicitBinder "(" [`y₂] [] [] ")")
                       (Term.explicitBinder
                        "("
                        [(Term.hole "_")]
                        [":"
                         («term_∈_» `y₂ "∈" («term_∩_» (Term.app `closed_ball [`x `δ]) "∩" `I.Icc))]
                        []
                        ")")]
                      []
                      ","
                      («term_≤_»
                       (Analysis.Normed.Group.Basic.«term‖_‖»
                        "‖"
                        («term_-_» (Term.app `f [`y₁]) "-" (Term.app `f [`y₂]))
                        "‖")
                       "≤"
                       («term_/_» `ε "/" (num "2"))))
                     "∧"
                     («term_≤_»
                      («term_*_»
                       («term_^_» («term_*_» (num "2") "*" `δ) "^" («term_+_» `n "+" (num "1")))
                       "*"
                       (Analysis.Normed.Group.Basic.«term‖_‖»
                        "‖"
                        (Term.app `f' [`x (Term.app `Pi.single [`i (num "1")])])
                        "‖"))
                      "≤"
                      («term_/_» `ε "/" (num "2")))))))]
                ":="
                (Term.byTactic
                 "by"
                 (Tactic.tacticSeq
                  (Tactic.tacticSeq1Indented
                   [(Tactic.refine'
                     "refine'"
                     (Term.app
                      `eventually.and
                      [(Term.hole "_")
                       (Term.app `eventually.and [(Term.hole "_") (Term.hole "_")])]))
                    []
                    (tactic__
                     (cdotTk (patternIgnore (token.«· » "·")))
                     [(Tactic.exact
                       "exact"
                       (Term.app
                        `Ioc_mem_nhds_within_Ioi
                        [(Term.anonymousCtor "⟨" [`le_rfl "," `one_half_pos] "⟩")]))])
                    []
                    (tactic__
                     (cdotTk (patternIgnore (token.«· » "·")))
                     [(Std.Tactic.rcases
                       "rcases"
                       [(Tactic.casesTarget
                         []
                         (Term.app
                          (Term.proj
                           (Term.app
                            (Term.proj
                             (Term.app
                              `nhds_within_has_basis
                              [`nhds_basis_closed_ball (Term.hole "_")])
                             "."
                             `tendsto_iff)
                            [`nhds_basis_closed_ball])
                           "."
                           (fieldIdx "1"))
                          [(Term.app `Hs [`x (Term.proj `hx "." (fieldIdx "2"))])
                           (Term.hole "_")
                           («term_<|_» `half_pos "<|" (Term.app `half_pos [`ε0]))]))]
                       ["with"
                        (Std.Tactic.RCases.rcasesPatLo
                         (Std.Tactic.RCases.rcasesPatMed
                          [(Std.Tactic.RCases.rcasesPat.tuple
                            "⟨"
                            [(Std.Tactic.RCases.rcasesPatLo
                              (Std.Tactic.RCases.rcasesPatMed
                               [(Std.Tactic.RCases.rcasesPat.one `δ₁)])
                              [])
                             ","
                             (Std.Tactic.RCases.rcasesPatLo
                              (Std.Tactic.RCases.rcasesPatMed
                               [(Std.Tactic.RCases.rcasesPat.one `δ₁0)])
                              [])
                             ","
                             (Std.Tactic.RCases.rcasesPatLo
                              (Std.Tactic.RCases.rcasesPatMed
                               [(Std.Tactic.RCases.rcasesPat.one `hδ₁)])
                              [])]
                            "⟩")])
                         [])])
                      []
                      (Tactic.filterUpwards
                       "filter_upwards"
                       [(Tactic.termList
                         "["
                         [(Term.app
                           `Ioc_mem_nhds_within_Ioi
                           [(Term.anonymousCtor "⟨" [`le_rfl "," `δ₁0] "⟩")])]
                         "]")]
                       ["with" [`δ `hδ `y₁ `hy₁ `y₂ `hy₂]]
                       [])
                      []
                      (Tactic.tacticHave_
                       "have"
                       (Term.haveDecl
                        (Term.haveIdDecl
                         []
                         [(Term.typeSpec
                           ":"
                           («term_⊆_»
                            («term_∩_» (Term.app `closed_ball [`x `δ]) "∩" `I.Icc)
                            "⊆"
                            («term_∩_» (Term.app `closed_ball [`x `δ₁]) "∩" `I.Icc)))]
                         ":="
                         (Term.app
                          `inter_subset_inter_left
                          [(Term.hole "_")
                           (Term.app
                            `closed_ball_subset_closed_ball
                            [(Term.proj `hδ "." (fieldIdx "2"))])]))))
                      []
                      (Tactic.rwSeq
                       "rw"
                       []
                       (Tactic.rwRuleSeq
                        "["
                        [(Tactic.rwRule [(patternIgnore (token.«← » "←"))] `dist_eq_norm)]
                        "]")
                       [])
                      []
                      (calcTactic
                       "calc"
                       (calcStep
                        («term_≤_»
                         (Term.app `dist [(Term.app `f [`y₁]) (Term.app `f [`y₂])])
                         "≤"
                         («term_+_»
                          (Term.app `dist [(Term.app `f [`y₁]) (Term.app `f [`x])])
                          "+"
                          (Term.app `dist [(Term.app `f [`y₂]) (Term.app `f [`x])])))
                        ":="
                        (Term.app
                         `dist_triangle_right
                         [(Term.hole "_") (Term.hole "_") (Term.hole "_")]))
                       [(calcStep
                         («term_≤_»
                          (Term.hole "_")
                          "≤"
                          («term_+_»
                           («term_/_» («term_/_» `ε "/" (num "2")) "/" (num "2"))
                           "+"
                           («term_/_» («term_/_» `ε "/" (num "2")) "/" (num "2"))))
                         ":="
                         (Term.app
                          `add_le_add
                          [(«term_<|_»
                            (Term.app `hδ₁ [(Term.hole "_")])
                            "<|"
                            (Term.app `this [`hy₁]))
                           («term_<|_»
                            (Term.app `hδ₁ [(Term.hole "_")])
                            "<|"
                            (Term.app `this [`hy₂]))]))
                        (calcStep
                         («term_=_» (Term.hole "_") "=" («term_/_» `ε "/" (num "2")))
                         ":="
                         (Term.app `add_halves [(Term.hole "_")]))])])
                    []
                    (tactic__
                     (cdotTk (patternIgnore (token.«· » "·")))
                     [(Tactic.tacticHave_
                       "have"
                       (Term.haveDecl
                        (Term.haveIdDecl
                         []
                         [(Term.typeSpec
                           ":"
                           (Term.app
                            `ContinuousWithinAt
                            [(Term.fun
                              "fun"
                              (Term.basicFun
                               [`δ]
                               []
                               "=>"
                               («term_*_»
                                («term_^_»
                                 («term_*_» (num "2") "*" `δ)
                                 "^"
                                 («term_+_» `n "+" (num "1")))
                                "*"
                                (Analysis.Normed.Group.Basic.«term‖_‖»
                                 "‖"
                                 (Term.app `f' [`x (Term.app `Pi.single [`i (num "1")])])
                                 "‖"))))
                             (Term.app
                              `Ioi
                              [(Term.typeAscription
                                "("
                                (num "0")
                                ":"
                                [(Data.Real.Basic.termℝ "ℝ")]
                                ")")])
                             (num "0")]))]
                         ":="
                         (Term.app
                          (Term.proj
                           (Term.app
                            (Term.proj
                             (Term.app `continuous_within_at_id.const_mul [(Term.hole "_")])
                             "."
                             `pow)
                            [(Term.hole "_")])
                           "."
                           `mul_const)
                          [(Term.hole "_")]))))
                      []
                      (Tactic.refine'
                       "refine'"
                       (Term.app `this.eventually [(Term.app `ge_mem_nhds [(Term.hole "_")])]))
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
                        ["using" (Term.app `half_pos [`ε0])]))])]))))))
             []
             (Std.Tactic.rcases
              "rcases"
              [(Tactic.casesTarget [] `this.exists)]
              ["with"
               (Std.Tactic.RCases.rcasesPatLo
                (Std.Tactic.RCases.rcasesPatMed
                 [(Std.Tactic.RCases.rcasesPat.tuple
                   "⟨"
                   [(Std.Tactic.RCases.rcasesPatLo
                     (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `δ)])
                     [])
                    ","
                    (Std.Tactic.RCases.rcasesPatLo
                     (Std.Tactic.RCases.rcasesPatMed
                      [(Std.Tactic.RCases.rcasesPat.tuple
                        "⟨"
                        [(Std.Tactic.RCases.rcasesPatLo
                          (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `hδ0)])
                          [])
                         ","
                         (Std.Tactic.RCases.rcasesPatLo
                          (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `hδ12)])
                          [])]
                        "⟩")])
                     [])
                    ","
                    (Std.Tactic.RCases.rcasesPatLo
                     (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `hdfδ)])
                     [])
                    ","
                    (Std.Tactic.RCases.rcasesPatLo
                     (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `hδ)])
                     [])]
                   "⟩")])
                [])])
             []
             (Tactic.refine'
              "refine'"
              (Term.anonymousCtor
               "⟨"
               [`δ
                ","
                `hδ0
                ","
                (Term.fun
                 "fun"
                 (Term.basicFun
                  [`J `hJI `hJδ `hxJ `hJc]
                  []
                  "=>"
                  (Term.subst (Term.app `add_halves [`ε]) "▸" [(Term.hole "_")])))]
               "⟩"))
             []
             (Tactic.tacticHave_
              "have"
              (Term.haveDecl
               (Term.haveIdDecl
                [`Hl []]
                [(Term.typeSpec
                  ":"
                  («term_∈_»
                   (Term.app `J.lower [`i])
                   "∈"
                   (Term.app `Icc [(Term.app `J.lower [`i]) (Term.app `J.upper [`i])])))]
                ":="
                (Term.app
                 (Term.proj `Set.left_mem_Icc "." (fieldIdx "2"))
                 [(Term.app `J.lower_le_upper [`i])]))))
             []
             (Tactic.tacticHave_
              "have"
              (Term.haveDecl
               (Term.haveIdDecl
                [`Hu []]
                [(Term.typeSpec
                  ":"
                  («term_∈_»
                   (Term.app `J.upper [`i])
                   "∈"
                   (Term.app `Icc [(Term.app `J.lower [`i]) (Term.app `J.upper [`i])])))]
                ":="
                (Term.app
                 (Term.proj `Set.right_mem_Icc "." (fieldIdx "2"))
                 [(Term.app `J.lower_le_upper [`i])]))))
             []
             (Tactic.tacticHave_
              "have"
              (Term.haveDecl
               (Term.haveIdDecl
                [`Hi []]
                [(Term.typeSpec
                  ":"
                  (Std.ExtendedBinder.«term∀__,_»
                   "∀"
                   (Lean.binderIdent `x)
                   («binderTerm∈_»
                    "∈"
                    (Term.app `Icc [(Term.app `J.lower [`i]) (Term.app `J.upper [`i])]))
                   ","
                   (Term.app
                    (Term.explicitUniv `Integrable ".{" [(num "0") "," `u "," `u] "}")
                    [(Term.app `J.face [`i])
                     `GP
                     (Term.fun
                      "fun"
                      (Term.basicFun [`y] [] "=>" (Term.app `f [(Term.app `i.insert_nth [`x `y])])))
                     `box_additive_map.volume])))]
                ":="
                (Term.fun
                 "fun"
                 (Term.basicFun
                  [`x `hx]
                  []
                  "=>"
                  (Term.app
                   `integrable_of_continuous_on
                   [(Term.hole "_")
                    (Term.app
                     `box.continuous_on_face_Icc
                     [(«term_<|_»
                       `Hc.mono
                       "<|"
                       (Term.app (Term.proj `box.le_iff_Icc "." (fieldIdx "1")) [`hJI]))
                      `hx])
                    `volume]))))))
             []
             (Tactic.tacticHave_
              "have"
              (Term.haveDecl
               (Term.haveIdDecl
                [`hJδ' []]
                [(Term.typeSpec
                  ":"
                  («term_⊆_» `J.Icc "⊆" («term_∩_» (Term.app `closed_ball [`x `δ]) "∩" `I.Icc)))]
                ":="
                (Term.app
                 `subset_inter
                 [`hJδ (Term.app (Term.proj `box.le_iff_Icc "." (fieldIdx "1")) [`hJI])]))))
             []
             (Tactic.tacticHave_
              "have"
              (Term.haveDecl
               (Term.haveIdDecl
                [`Hmaps []]
                [(Term.typeSpec
                  ":"
                  (Std.ExtendedBinder.«term∀__,_»
                   "∀"
                   (Lean.binderIdent `z)
                   («binderTerm∈_»
                    "∈"
                    (Term.app `Icc [(Term.app `J.lower [`i]) (Term.app `J.upper [`i])]))
                   ","
                   (Term.app
                    `maps_to
                    [(Term.app `i.insert_nth [`z])
                     (Term.proj (Term.app `J.face [`i]) "." `IccCat)
                     («term_∩_» (Term.app `closed_ball [`x `δ]) "∩" `I.Icc)])))]
                ":="
                (Term.fun
                 "fun"
                 (Term.basicFun
                  [`z `hz]
                  []
                  "=>"
                  (Term.app
                   (Term.proj (Term.app `J.maps_to_insert_nth_face_Icc [`hz]) "." `mono)
                   [`subset.rfl `hJδ']))))))
             []
             (Tactic.simp
              "simp"
              []
              []
              ["only"]
              ["["
               [(Tactic.simpLemma [] [] `dist_eq_norm)
                ","
                (Tactic.simpLemma [] [] `F)
                ","
                (Tactic.simpLemma [] [] `fI)]
               "]"]
              [])
             []
             (Tactic.dsimp "dsimp" [] [] [] [] [])
             []
             (Tactic.rwSeq
              "rw"
              []
              (Tactic.rwRuleSeq
               "["
               [(Tactic.rwRule
                 [(patternIgnore (token.«← » "←"))]
                 (Term.app
                  `integral_sub
                  [(Term.app `Hi [(Term.hole "_") `Hu]) (Term.app `Hi [(Term.hole "_") `Hl])]))]
               "]")
              [])
             []
             (Tactic.refine'
              "refine'"
              (Term.app
               (Term.proj (Term.app `norm_sub_le [(Term.hole "_") (Term.hole "_")]) "." `trans)
               [(Term.app `add_le_add [(Term.hole "_") (Term.hole "_")])]))
             []
             (tactic__
              (cdotTk (patternIgnore (token.«· » "·")))
              [(Mathlib.Tactic.tacticSimp_rw__
                "simp_rw"
                (Tactic.rwRuleSeq
                 "["
                 [(Tactic.rwRule [] `box_additive_map.volume_apply)
                  ","
                  (Tactic.rwRule [] `norm_smul)
                  ","
                  (Tactic.rwRule [] `Real.norm_eq_abs)
                  ","
                  (Tactic.rwRule [] `abs_prod)]
                 "]")
                [])
               []
               (Tactic.refine'
                "refine'"
                (Term.app
                 (Term.proj
                  («term_<|_»
                   (Term.app `mul_le_mul_of_nonneg_right [(Term.hole "_")])
                   "<|"
                   (Term.app `norm_nonneg [(Term.hole "_")]))
                  "."
                  `trans)
                 [`hδ]))
               []
               (Tactic.tacticHave_
                "have"
                (Term.haveDecl
                 (Term.haveIdDecl
                  []
                  [(Term.typeSpec
                    ":"
                    (Term.forall
                     "∀"
                     [`j]
                     []
                     ","
                     («term_≤_»
                      («term|___|»
                       (group "|")
                       («term_-_» (Term.app `J.upper [`j]) "-" (Term.app `J.lower [`j]))
                       (group)
                       "|")
                      "≤"
                      («term_*_» (num "2") "*" `δ))))]
                  ":="
                  (Term.byTactic
                   "by"
                   (Tactic.tacticSeq
                    (Tactic.tacticSeq1Indented
                     [(Tactic.intro "intro" [`j])
                      []
                      (calcTactic
                       "calc"
                       (calcStep
                        («term_≤_»
                         (Term.app `dist [(Term.app `J.upper [`j]) (Term.app `J.lower [`j])])
                         "≤"
                         (Term.app `dist [`J.upper `J.lower]))
                        ":="
                        (Term.app
                         `dist_le_pi_dist
                         [(Term.hole "_") (Term.hole "_") (Term.hole "_")]))
                       [(calcStep
                         («term_≤_»
                          (Term.hole "_")
                          "≤"
                          («term_+_»
                           (Term.app `dist [`J.upper `x])
                           "+"
                           (Term.app `dist [`J.lower `x])))
                         ":="
                         (Term.app
                          `dist_triangle_right
                          [(Term.hole "_") (Term.hole "_") (Term.hole "_")]))
                        (calcStep
                         («term_≤_» (Term.hole "_") "≤" («term_+_» `δ "+" `δ))
                         ":="
                         (Term.app
                          `add_le_add
                          [(Term.app `hJδ [`J.upper_mem_Icc]) (Term.app `hJδ [`J.lower_mem_Icc])]))
                        (calcStep
                         («term_=_» (Term.hole "_") "=" («term_*_» (num "2") "*" `δ))
                         ":="
                         (Term.proj (Term.app `two_mul [`δ]) "." `symm))])]))))))
               []
               (calcTactic
                "calc"
                (calcStep
                 («term_≤_»
                  (BigOperators.Algebra.BigOperators.Basic.finset.prod_univ
                   "∏"
                   (Std.ExtendedBinder.extBinders
                    (Std.ExtendedBinder.extBinder (Lean.binderIdent `j) []))
                   ", "
                   («term|___|»
                    (group "|")
                    («term_-_» (Term.app `J.upper [`j]) "-" (Term.app `J.lower [`j]))
                    (group)
                    "|"))
                  "≤"
                  (BigOperators.Algebra.BigOperators.Basic.finset.prod_univ
                   "∏"
                   (Std.ExtendedBinder.extBinders
                    (Std.ExtendedBinder.extBinder
                     (Lean.binderIdent `j)
                     [(group ":" (Term.app `Fin [(«term_+_» `n "+" (num "1"))]))]))
                   ", "
                   («term_*_» (num "2") "*" `δ)))
                 ":="
                 (Term.app
                  `prod_le_prod
                  [(Term.fun
                    "fun"
                    (Term.basicFun
                     [(Term.hole "_") (Term.hole "_")]
                     []
                     "=>"
                     (Term.app `abs_nonneg [(Term.hole "_")])))
                   (Term.fun "fun" (Term.basicFun [`j `hj] [] "=>" (Term.app `this [`j])))]))
                [(calcStep
                  («term_=_»
                   (Term.hole "_")
                   "="
                   («term_^_» («term_*_» (num "2") "*" `δ) "^" («term_+_» `n "+" (num "1"))))
                  ":="
                  (Term.byTactic
                   "by"
                   (Tactic.tacticSeq
                    (Tactic.tacticSeq1Indented [(Tactic.simp "simp" [] [] [] [] [])]))))])])
             []
             (tactic__
              (cdotTk (patternIgnore (token.«· » "·")))
              [(Tactic.refine'
                "refine'"
                (Term.app
                 (Term.proj
                  (Term.app
                   `norm_integral_le_of_le_const
                   [(Term.fun
                     "fun"
                     (Term.basicFun
                      [`y `hy]
                      []
                      "=>"
                      (Term.app
                       `hdfδ
                       [(Term.hole "_")
                        (Term.app `Hmaps [(Term.hole "_") `Hu `hy])
                        (Term.hole "_")
                        (Term.app `Hmaps [(Term.hole "_") `Hl `hy])])))
                    (Term.hole "_")])
                  "."
                  `trans)
                 [(Term.hole "_")]))
               []
               (Tactic.refine'
                "refine'"
                (Term.app
                 (Term.proj
                  (Term.app
                   `mul_le_mul_of_nonneg_right
                   [(Term.hole "_") (Term.proj (Term.app `half_pos [`ε0]) "." `le)])
                  "."
                  `trans_eq)
                 [(Term.app `one_mul [(Term.hole "_")])]))
               []
               (Tactic.rwSeq
                "rw"
                []
                (Tactic.rwRuleSeq
                 "["
                 [(Tactic.rwRule [] `box.coe_eq_pi)
                  ","
                  (Tactic.rwRule
                   []
                   (Term.app
                    `Real.volume_pi_Ioc_to_real
                    [(Term.app `box.lower_le_upper [(Term.hole "_")])]))]
                 "]")
                [])
               []
               (Tactic.refine'
                "refine'"
                (Term.app
                 `prod_le_one
                 [(Term.fun
                   "fun"
                   (Term.basicFun
                    [(Term.hole "_") (Term.hole "_")]
                    []
                    "=>"
                    («term_<|_»
                     (Term.proj `sub_nonneg "." (fieldIdx "2"))
                     "<|"
                     (Term.app `box.lower_le_upper [(Term.hole "_") (Term.hole "_")]))))
                  (Term.fun "fun" (Term.basicFun [`j `hj] [] "=>" (Term.hole "_")))]))
               []
               (calcTactic
                "calc"
                (calcStep
                 («term_≤_»
                  («term_-_»
                   (Term.app `J.upper [(Term.app `i.succ_above [`j])])
                   "-"
                   (Term.app `J.lower [(Term.app `i.succ_above [`j])]))
                  "≤"
                  (Term.app
                   `dist
                   [(Term.app `J.upper [(Term.app `i.succ_above [`j])])
                    (Term.app `J.lower [(Term.app `i.succ_above [`j])])]))
                 ":="
                 (Term.app `le_abs_self [(Term.hole "_")]))
                [(calcStep
                  («term_≤_» (Term.hole "_") "≤" (Term.app `dist [`J.upper `J.lower]))
                  ":="
                  (Term.app `dist_le_pi_dist [`J.upper `J.lower (Term.app `i.succ_above [`j])]))
                 (calcStep
                  («term_≤_»
                   (Term.hole "_")
                   "≤"
                   («term_+_» (Term.app `dist [`J.upper `x]) "+" (Term.app `dist [`J.lower `x])))
                  ":="
                  (Term.app `dist_triangle_right [(Term.hole "_") (Term.hole "_") (Term.hole "_")]))
                 (calcStep
                  («term_≤_» (Term.hole "_") "≤" («term_+_» `δ "+" `δ))
                  ":="
                  (Term.app
                   `add_le_add
                   [(Term.app `hJδ [`J.upper_mem_Icc]) (Term.app `hJδ [`J.lower_mem_Icc])]))
                 (calcStep
                  («term_≤_»
                   (Term.hole "_")
                   "≤"
                   («term_+_»
                    («term_/_» (num "1") "/" (num "2"))
                    "+"
                    («term_/_» (num "1") "/" (num "2"))))
                  ":="
                  (Term.app `add_le_add [`hδ12 `hδ12]))
                 (calcStep
                  («term_=_» (Term.hole "_") "=" (num "1"))
                  ":="
                  (Term.app `add_halves [(num "1")]))])])])
           []
           (tactic__
            (cdotTk (patternIgnore (token.«· » "·")))
            [(Tactic.intro "intro" [`c `x `hx `ε `ε0])
             []
             (Std.Tactic.rcases
              "rcases"
              [(Tactic.casesTarget
                []
                (Term.app `exists_pos_mul_lt [`ε0 («term_*_» (num "2") "*" `c)]))]
              ["with"
               (Std.Tactic.RCases.rcasesPatLo
                (Std.Tactic.RCases.rcasesPatMed
                 [(Std.Tactic.RCases.rcasesPat.tuple
                   "⟨"
                   [(Std.Tactic.RCases.rcasesPatLo
                     (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `ε')])
                     [])
                    ","
                    (Std.Tactic.RCases.rcasesPatLo
                     (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `ε'0)])
                     [])
                    ","
                    (Std.Tactic.RCases.rcasesPatLo
                     (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `hlt)])
                     [])]
                   "⟩")])
                [])])
             []
             (Std.Tactic.rcases
              "rcases"
              [(Tactic.casesTarget
                []
                (Term.app
                 (Term.proj
                  (Term.proj
                   (Term.app `nhds_within_has_basis [`nhds_basis_closed_ball (Term.hole "_")])
                   "."
                   `mem_iff)
                  "."
                  (fieldIdx "1"))
                 [(Term.app (Term.proj (Term.app `Hd [`x `hx]) "." `def) [`ε'0])]))]
              ["with"
               (Std.Tactic.RCases.rcasesPatLo
                (Std.Tactic.RCases.rcasesPatMed
                 [(Std.Tactic.RCases.rcasesPat.tuple
                   "⟨"
                   [(Std.Tactic.RCases.rcasesPatLo
                     (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `δ)])
                     [])
                    ","
                    (Std.Tactic.RCases.rcasesPatLo
                     (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `δ0)])
                     [])
                    ","
                    (Std.Tactic.RCases.rcasesPatLo
                     (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `Hδ)])
                     [])]
                   "⟩")])
                [])])
             []
             (Tactic.refine'
              "refine'"
              (Term.anonymousCtor
               "⟨"
               [`δ
                ","
                `δ0
                ","
                (Term.fun "fun" (Term.basicFun [`J `hle `hJδ `hxJ `hJc] [] "=>" (Term.hole "_")))]
               "⟩"))
             []
             (Tactic.simp
              "simp"
              []
              []
              ["only"]
              ["["
               [(Tactic.simpLemma [] [] `box_additive_map.volume_apply)
                ","
                (Tactic.simpLemma [] [] `box.volume_apply)
                ","
                (Tactic.simpLemma [] [] `dist_eq_norm)]
               "]"]
              [])
             []
             (Tactic.refine'
              "refine'"
              (Term.app
               (Term.proj
                (Term.app
                 `norm_volume_sub_integral_face_upper_sub_lower_smul_le
                 [(Term.hole "_")
                  («term_<|_»
                   `Hc.mono
                   "<|"
                   (Term.app (Term.proj `box.le_iff_Icc "." (fieldIdx "1")) [`hle]))
                  `hxJ
                  `ε'0
                  (Term.fun "fun" (Term.basicFun [`y `hy] [] "=>" (Term.app `Hδ [(Term.hole "_")])))
                  (Term.app `hJc [`rfl])])
                "."
                `trans)
               [(Term.hole "_")]))
             []
             (tactic__
              (cdotTk (patternIgnore (token.«· » "·")))
              [(Tactic.exact
                "exact"
                (Term.anonymousCtor
                 "⟨"
                 [(Term.app `hJδ [`hy])
                  ","
                  (Term.app (Term.proj `box.le_iff_Icc "." (fieldIdx "1")) [`hle `hy])]
                 "⟩"))])
             []
             (tactic__
              (cdotTk (patternIgnore (token.«· » "·")))
              [(Tactic.rwSeq
                "rw"
                []
                (Tactic.rwRuleSeq
                 "["
                 [(Tactic.rwRule
                   []
                   (Term.app
                    `mul_right_comm
                    [(Term.typeAscription "(" (num "2") ":" [(Data.Real.Basic.termℝ "ℝ")] ")")]))
                  ","
                  (Tactic.rwRule [(patternIgnore (token.«← » "←"))] `box.volume_apply)]
                 "]")
                [])
               []
               (Tactic.exact
                "exact"
                (Term.app `mul_le_mul_of_nonneg_right [`hlt.le `Ennreal.to_real_nonneg]))])])])))
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
         [(Tactic.tacticHave_
           "have"
           (Term.haveDecl
            (Term.haveIdDecl
             [`Hc []]
             [(Term.typeSpec ":" (Term.app `ContinuousOn [`f `I.Icc]))]
             ":="
             (Term.byTactic
              "by"
              (Tactic.tacticSeq
               (Tactic.tacticSeq1Indented
                [(Tactic.intro "intro" [`x `hx])
                 []
                 (Classical.«tacticBy_cases_:_» "by_cases" [`hxs ":"] («term_∈_» `x "∈" `s))
                 []
                 (Std.Tactic.exacts
                  "exacts"
                  "["
                  [(Term.app `Hs [`x `hxs])
                   ","
                   (Term.proj
                    (Term.app `Hd [`x (Term.anonymousCtor "⟨" [`hx "," `hxs] "⟩")])
                    "."
                    `ContinuousWithinAt)]
                  "]")]))))))
          []
          (Mathlib.Tactic.set
           "set"
           []
           (Mathlib.Tactic.setArgsRest
            `fI
            [":"
             (Term.arrow
              (Data.Real.Basic.termℝ "ℝ")
              "→"
              (Term.arrow (Term.app `box [(Term.app `Fin [`n])]) "→" `E))]
            ":="
            (Term.fun
             "fun"
             (Term.basicFun
              [`y `J]
              []
              "=>"
              (Term.app
               (Term.explicitUniv `integral ".{" [(num "0") "," `u "," `u] "}")
               [`J
                `GP
                (Term.fun
                 "fun"
                 (Term.basicFun [`x] [] "=>" (Term.app `f [(Term.app `i.insert_nth [`y `x])])))
                `box_additive_map.volume])))
            []))
          []
          (Mathlib.Tactic.set
           "set"
           []
           (Mathlib.Tactic.setArgsRest
            `fb
            [":"
             (Term.arrow
              (Term.app `Icc [(Term.app `I.lower [`i]) (Term.app `I.upper [`i])])
              "→"
              (BoxIntegral.Analysis.BoxIntegral.Partition.Additive.box_integral.box_additive_map
               (Term.app `Fin [`n])
               " →ᵇᵃ["
               (coeNotation "↑" (Term.app `I.face [`i]))
               "] "
               `E))]
            ":="
            (Term.fun
             "fun"
             (Term.basicFun
              [`x]
              []
              "=>"
              (Term.proj
               (Term.app
                `integrable_of_continuous_on
                [`GP
                 (Term.app `box.continuous_on_face_Icc [`Hc (Term.proj `x "." (fieldIdx "2"))])
                 `volume])
               "."
               `toBoxAdditive)))
            []))
          []
          (Mathlib.Tactic.set
           "set"
           []
           (Mathlib.Tactic.setArgsRest
            `F
            [":"
             (BoxIntegral.Analysis.BoxIntegral.Partition.Additive.box_integral.box_additive_map
              (Term.app `Fin [(«term_+_» `n "+" (num "1"))])
              " →ᵇᵃ["
              `I
              "] "
              `E)]
            ":="
            (Term.app
             `box_additive_map.upper_sub_lower
             [`I `i `fI `fb (Term.fun "fun" (Term.basicFun [`x `hx `J] [] "=>" `rfl))])
            []))
          []
          (Tactic.change
           "change"
           (Term.app
            `has_integral
            [`I
             `GP
             (Term.fun
              "fun"
              (Term.basicFun [`x] [] "=>" (Term.app `f' [`x (Term.app `Pi.single [`i (num "1")])])))
             (Term.hole "_")
             (Term.app `F [`I])])
           [])
          []
          (Tactic.refine'
           "refine'"
           (Term.app
            `has_integral_of_le_Henstock_of_forall_is_o
            [`GP_le
             (Term.hole "_")
             (Term.hole "_")
             (Term.hole "_")
             `s
             `hs
             (Term.hole "_")
             (Term.hole "_")]))
          []
          (tactic__
           (cdotTk (patternIgnore (token.«· » "·")))
           [(Tactic.exact
             "exact"
             (Term.app
              (Term.proj
               (Term.proj
                (Term.typeAscription
                 "("
                 `volume
                 ":"
                 [(Term.app
                   `Measure
                   [(BoxIntegral.Analysis.BoxIntegral.DivergenceTheorem.«termℝⁿ⁺¹» "ℝⁿ⁺¹")])]
                 ")")
                "."
                `toBoxAdditive)
               "."
               `restrict)
              [(Term.hole "_") `le_top]))])
          []
          (tactic__
           (cdotTk (patternIgnore (token.«· » "·")))
           [(Tactic.exact
             "exact"
             (Term.fun "fun" (Term.basicFun [`J] [] "=>" `Ennreal.to_real_nonneg)))])
          []
          (tactic__
           (cdotTk (patternIgnore (token.«· » "·")))
           [(Tactic.intro "intro" [`c `x `hx `ε `ε0])
            []
            (Tactic.tacticHave_
             "have"
             (Term.haveDecl
              (Term.haveIdDecl
               []
               [(Term.typeSpec
                 ":"
                 (Filter.Order.Filter.Basic.«term∀ᶠ_in_,_»
                  "∀ᶠ"
                  (Std.ExtendedBinder.extBinders
                   (Std.ExtendedBinder.extBinder (Lean.binderIdent `δ) []))
                  " in "
                  (TopologicalSpace.Topology.Basic.nhds_within.gt
                   "𝓝[>] "
                   (Term.typeAscription "(" (num "0") ":" [(Data.Real.Basic.termℝ "ℝ")] ")"))
                  ", "
                  («term_∧_»
                   («term_∈_»
                    `δ
                    "∈"
                    (Term.app
                     `Ioc
                     [(Term.typeAscription "(" (num "0") ":" [(Data.Real.Basic.termℝ "ℝ")] ")")
                      («term_/_» (num "1") "/" (num "2"))]))
                   "∧"
                   («term_∧_»
                    (Term.forall
                     "∀"
                     [(Term.explicitBinder "(" [`y₁] [] [] ")")
                      (Term.explicitBinder
                       "("
                       [(Term.hole "_")]
                       [":"
                        («term_∈_» `y₁ "∈" («term_∩_» (Term.app `closed_ball [`x `δ]) "∩" `I.Icc))]
                       []
                       ")")
                      (Term.explicitBinder "(" [`y₂] [] [] ")")
                      (Term.explicitBinder
                       "("
                       [(Term.hole "_")]
                       [":"
                        («term_∈_» `y₂ "∈" («term_∩_» (Term.app `closed_ball [`x `δ]) "∩" `I.Icc))]
                       []
                       ")")]
                     []
                     ","
                     («term_≤_»
                      (Analysis.Normed.Group.Basic.«term‖_‖»
                       "‖"
                       («term_-_» (Term.app `f [`y₁]) "-" (Term.app `f [`y₂]))
                       "‖")
                      "≤"
                      («term_/_» `ε "/" (num "2"))))
                    "∧"
                    («term_≤_»
                     («term_*_»
                      («term_^_» («term_*_» (num "2") "*" `δ) "^" («term_+_» `n "+" (num "1")))
                      "*"
                      (Analysis.Normed.Group.Basic.«term‖_‖»
                       "‖"
                       (Term.app `f' [`x (Term.app `Pi.single [`i (num "1")])])
                       "‖"))
                     "≤"
                     («term_/_» `ε "/" (num "2")))))))]
               ":="
               (Term.byTactic
                "by"
                (Tactic.tacticSeq
                 (Tactic.tacticSeq1Indented
                  [(Tactic.refine'
                    "refine'"
                    (Term.app
                     `eventually.and
                     [(Term.hole "_")
                      (Term.app `eventually.and [(Term.hole "_") (Term.hole "_")])]))
                   []
                   (tactic__
                    (cdotTk (patternIgnore (token.«· » "·")))
                    [(Tactic.exact
                      "exact"
                      (Term.app
                       `Ioc_mem_nhds_within_Ioi
                       [(Term.anonymousCtor "⟨" [`le_rfl "," `one_half_pos] "⟩")]))])
                   []
                   (tactic__
                    (cdotTk (patternIgnore (token.«· » "·")))
                    [(Std.Tactic.rcases
                      "rcases"
                      [(Tactic.casesTarget
                        []
                        (Term.app
                         (Term.proj
                          (Term.app
                           (Term.proj
                            (Term.app
                             `nhds_within_has_basis
                             [`nhds_basis_closed_ball (Term.hole "_")])
                            "."
                            `tendsto_iff)
                           [`nhds_basis_closed_ball])
                          "."
                          (fieldIdx "1"))
                         [(Term.app `Hs [`x (Term.proj `hx "." (fieldIdx "2"))])
                          (Term.hole "_")
                          («term_<|_» `half_pos "<|" (Term.app `half_pos [`ε0]))]))]
                      ["with"
                       (Std.Tactic.RCases.rcasesPatLo
                        (Std.Tactic.RCases.rcasesPatMed
                         [(Std.Tactic.RCases.rcasesPat.tuple
                           "⟨"
                           [(Std.Tactic.RCases.rcasesPatLo
                             (Std.Tactic.RCases.rcasesPatMed
                              [(Std.Tactic.RCases.rcasesPat.one `δ₁)])
                             [])
                            ","
                            (Std.Tactic.RCases.rcasesPatLo
                             (Std.Tactic.RCases.rcasesPatMed
                              [(Std.Tactic.RCases.rcasesPat.one `δ₁0)])
                             [])
                            ","
                            (Std.Tactic.RCases.rcasesPatLo
                             (Std.Tactic.RCases.rcasesPatMed
                              [(Std.Tactic.RCases.rcasesPat.one `hδ₁)])
                             [])]
                           "⟩")])
                        [])])
                     []
                     (Tactic.filterUpwards
                      "filter_upwards"
                      [(Tactic.termList
                        "["
                        [(Term.app
                          `Ioc_mem_nhds_within_Ioi
                          [(Term.anonymousCtor "⟨" [`le_rfl "," `δ₁0] "⟩")])]
                        "]")]
                      ["with" [`δ `hδ `y₁ `hy₁ `y₂ `hy₂]]
                      [])
                     []
                     (Tactic.tacticHave_
                      "have"
                      (Term.haveDecl
                       (Term.haveIdDecl
                        []
                        [(Term.typeSpec
                          ":"
                          («term_⊆_»
                           («term_∩_» (Term.app `closed_ball [`x `δ]) "∩" `I.Icc)
                           "⊆"
                           («term_∩_» (Term.app `closed_ball [`x `δ₁]) "∩" `I.Icc)))]
                        ":="
                        (Term.app
                         `inter_subset_inter_left
                         [(Term.hole "_")
                          (Term.app
                           `closed_ball_subset_closed_ball
                           [(Term.proj `hδ "." (fieldIdx "2"))])]))))
                     []
                     (Tactic.rwSeq
                      "rw"
                      []
                      (Tactic.rwRuleSeq
                       "["
                       [(Tactic.rwRule [(patternIgnore (token.«← » "←"))] `dist_eq_norm)]
                       "]")
                      [])
                     []
                     (calcTactic
                      "calc"
                      (calcStep
                       («term_≤_»
                        (Term.app `dist [(Term.app `f [`y₁]) (Term.app `f [`y₂])])
                        "≤"
                        («term_+_»
                         (Term.app `dist [(Term.app `f [`y₁]) (Term.app `f [`x])])
                         "+"
                         (Term.app `dist [(Term.app `f [`y₂]) (Term.app `f [`x])])))
                       ":="
                       (Term.app
                        `dist_triangle_right
                        [(Term.hole "_") (Term.hole "_") (Term.hole "_")]))
                      [(calcStep
                        («term_≤_»
                         (Term.hole "_")
                         "≤"
                         («term_+_»
                          («term_/_» («term_/_» `ε "/" (num "2")) "/" (num "2"))
                          "+"
                          («term_/_» («term_/_» `ε "/" (num "2")) "/" (num "2"))))
                        ":="
                        (Term.app
                         `add_le_add
                         [(«term_<|_»
                           (Term.app `hδ₁ [(Term.hole "_")])
                           "<|"
                           (Term.app `this [`hy₁]))
                          («term_<|_»
                           (Term.app `hδ₁ [(Term.hole "_")])
                           "<|"
                           (Term.app `this [`hy₂]))]))
                       (calcStep
                        («term_=_» (Term.hole "_") "=" («term_/_» `ε "/" (num "2")))
                        ":="
                        (Term.app `add_halves [(Term.hole "_")]))])])
                   []
                   (tactic__
                    (cdotTk (patternIgnore (token.«· » "·")))
                    [(Tactic.tacticHave_
                      "have"
                      (Term.haveDecl
                       (Term.haveIdDecl
                        []
                        [(Term.typeSpec
                          ":"
                          (Term.app
                           `ContinuousWithinAt
                           [(Term.fun
                             "fun"
                             (Term.basicFun
                              [`δ]
                              []
                              "=>"
                              («term_*_»
                               («term_^_»
                                («term_*_» (num "2") "*" `δ)
                                "^"
                                («term_+_» `n "+" (num "1")))
                               "*"
                               (Analysis.Normed.Group.Basic.«term‖_‖»
                                "‖"
                                (Term.app `f' [`x (Term.app `Pi.single [`i (num "1")])])
                                "‖"))))
                            (Term.app
                             `Ioi
                             [(Term.typeAscription
                               "("
                               (num "0")
                               ":"
                               [(Data.Real.Basic.termℝ "ℝ")]
                               ")")])
                            (num "0")]))]
                        ":="
                        (Term.app
                         (Term.proj
                          (Term.app
                           (Term.proj
                            (Term.app `continuous_within_at_id.const_mul [(Term.hole "_")])
                            "."
                            `pow)
                           [(Term.hole "_")])
                          "."
                          `mul_const)
                         [(Term.hole "_")]))))
                     []
                     (Tactic.refine'
                      "refine'"
                      (Term.app `this.eventually [(Term.app `ge_mem_nhds [(Term.hole "_")])]))
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
                       ["using" (Term.app `half_pos [`ε0])]))])]))))))
            []
            (Std.Tactic.rcases
             "rcases"
             [(Tactic.casesTarget [] `this.exists)]
             ["with"
              (Std.Tactic.RCases.rcasesPatLo
               (Std.Tactic.RCases.rcasesPatMed
                [(Std.Tactic.RCases.rcasesPat.tuple
                  "⟨"
                  [(Std.Tactic.RCases.rcasesPatLo
                    (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `δ)])
                    [])
                   ","
                   (Std.Tactic.RCases.rcasesPatLo
                    (Std.Tactic.RCases.rcasesPatMed
                     [(Std.Tactic.RCases.rcasesPat.tuple
                       "⟨"
                       [(Std.Tactic.RCases.rcasesPatLo
                         (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `hδ0)])
                         [])
                        ","
                        (Std.Tactic.RCases.rcasesPatLo
                         (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `hδ12)])
                         [])]
                       "⟩")])
                    [])
                   ","
                   (Std.Tactic.RCases.rcasesPatLo
                    (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `hdfδ)])
                    [])
                   ","
                   (Std.Tactic.RCases.rcasesPatLo
                    (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `hδ)])
                    [])]
                  "⟩")])
               [])])
            []
            (Tactic.refine'
             "refine'"
             (Term.anonymousCtor
              "⟨"
              [`δ
               ","
               `hδ0
               ","
               (Term.fun
                "fun"
                (Term.basicFun
                 [`J `hJI `hJδ `hxJ `hJc]
                 []
                 "=>"
                 (Term.subst (Term.app `add_halves [`ε]) "▸" [(Term.hole "_")])))]
              "⟩"))
            []
            (Tactic.tacticHave_
             "have"
             (Term.haveDecl
              (Term.haveIdDecl
               [`Hl []]
               [(Term.typeSpec
                 ":"
                 («term_∈_»
                  (Term.app `J.lower [`i])
                  "∈"
                  (Term.app `Icc [(Term.app `J.lower [`i]) (Term.app `J.upper [`i])])))]
               ":="
               (Term.app
                (Term.proj `Set.left_mem_Icc "." (fieldIdx "2"))
                [(Term.app `J.lower_le_upper [`i])]))))
            []
            (Tactic.tacticHave_
             "have"
             (Term.haveDecl
              (Term.haveIdDecl
               [`Hu []]
               [(Term.typeSpec
                 ":"
                 («term_∈_»
                  (Term.app `J.upper [`i])
                  "∈"
                  (Term.app `Icc [(Term.app `J.lower [`i]) (Term.app `J.upper [`i])])))]
               ":="
               (Term.app
                (Term.proj `Set.right_mem_Icc "." (fieldIdx "2"))
                [(Term.app `J.lower_le_upper [`i])]))))
            []
            (Tactic.tacticHave_
             "have"
             (Term.haveDecl
              (Term.haveIdDecl
               [`Hi []]
               [(Term.typeSpec
                 ":"
                 (Std.ExtendedBinder.«term∀__,_»
                  "∀"
                  (Lean.binderIdent `x)
                  («binderTerm∈_»
                   "∈"
                   (Term.app `Icc [(Term.app `J.lower [`i]) (Term.app `J.upper [`i])]))
                  ","
                  (Term.app
                   (Term.explicitUniv `Integrable ".{" [(num "0") "," `u "," `u] "}")
                   [(Term.app `J.face [`i])
                    `GP
                    (Term.fun
                     "fun"
                     (Term.basicFun [`y] [] "=>" (Term.app `f [(Term.app `i.insert_nth [`x `y])])))
                    `box_additive_map.volume])))]
               ":="
               (Term.fun
                "fun"
                (Term.basicFun
                 [`x `hx]
                 []
                 "=>"
                 (Term.app
                  `integrable_of_continuous_on
                  [(Term.hole "_")
                   (Term.app
                    `box.continuous_on_face_Icc
                    [(«term_<|_»
                      `Hc.mono
                      "<|"
                      (Term.app (Term.proj `box.le_iff_Icc "." (fieldIdx "1")) [`hJI]))
                     `hx])
                   `volume]))))))
            []
            (Tactic.tacticHave_
             "have"
             (Term.haveDecl
              (Term.haveIdDecl
               [`hJδ' []]
               [(Term.typeSpec
                 ":"
                 («term_⊆_» `J.Icc "⊆" («term_∩_» (Term.app `closed_ball [`x `δ]) "∩" `I.Icc)))]
               ":="
               (Term.app
                `subset_inter
                [`hJδ (Term.app (Term.proj `box.le_iff_Icc "." (fieldIdx "1")) [`hJI])]))))
            []
            (Tactic.tacticHave_
             "have"
             (Term.haveDecl
              (Term.haveIdDecl
               [`Hmaps []]
               [(Term.typeSpec
                 ":"
                 (Std.ExtendedBinder.«term∀__,_»
                  "∀"
                  (Lean.binderIdent `z)
                  («binderTerm∈_»
                   "∈"
                   (Term.app `Icc [(Term.app `J.lower [`i]) (Term.app `J.upper [`i])]))
                  ","
                  (Term.app
                   `maps_to
                   [(Term.app `i.insert_nth [`z])
                    (Term.proj (Term.app `J.face [`i]) "." `IccCat)
                    («term_∩_» (Term.app `closed_ball [`x `δ]) "∩" `I.Icc)])))]
               ":="
               (Term.fun
                "fun"
                (Term.basicFun
                 [`z `hz]
                 []
                 "=>"
                 (Term.app
                  (Term.proj (Term.app `J.maps_to_insert_nth_face_Icc [`hz]) "." `mono)
                  [`subset.rfl `hJδ']))))))
            []
            (Tactic.simp
             "simp"
             []
             []
             ["only"]
             ["["
              [(Tactic.simpLemma [] [] `dist_eq_norm)
               ","
               (Tactic.simpLemma [] [] `F)
               ","
               (Tactic.simpLemma [] [] `fI)]
              "]"]
             [])
            []
            (Tactic.dsimp "dsimp" [] [] [] [] [])
            []
            (Tactic.rwSeq
             "rw"
             []
             (Tactic.rwRuleSeq
              "["
              [(Tactic.rwRule
                [(patternIgnore (token.«← » "←"))]
                (Term.app
                 `integral_sub
                 [(Term.app `Hi [(Term.hole "_") `Hu]) (Term.app `Hi [(Term.hole "_") `Hl])]))]
              "]")
             [])
            []
            (Tactic.refine'
             "refine'"
             (Term.app
              (Term.proj (Term.app `norm_sub_le [(Term.hole "_") (Term.hole "_")]) "." `trans)
              [(Term.app `add_le_add [(Term.hole "_") (Term.hole "_")])]))
            []
            (tactic__
             (cdotTk (patternIgnore (token.«· » "·")))
             [(Mathlib.Tactic.tacticSimp_rw__
               "simp_rw"
               (Tactic.rwRuleSeq
                "["
                [(Tactic.rwRule [] `box_additive_map.volume_apply)
                 ","
                 (Tactic.rwRule [] `norm_smul)
                 ","
                 (Tactic.rwRule [] `Real.norm_eq_abs)
                 ","
                 (Tactic.rwRule [] `abs_prod)]
                "]")
               [])
              []
              (Tactic.refine'
               "refine'"
               (Term.app
                (Term.proj
                 («term_<|_»
                  (Term.app `mul_le_mul_of_nonneg_right [(Term.hole "_")])
                  "<|"
                  (Term.app `norm_nonneg [(Term.hole "_")]))
                 "."
                 `trans)
                [`hδ]))
              []
              (Tactic.tacticHave_
               "have"
               (Term.haveDecl
                (Term.haveIdDecl
                 []
                 [(Term.typeSpec
                   ":"
                   (Term.forall
                    "∀"
                    [`j]
                    []
                    ","
                    («term_≤_»
                     («term|___|»
                      (group "|")
                      («term_-_» (Term.app `J.upper [`j]) "-" (Term.app `J.lower [`j]))
                      (group)
                      "|")
                     "≤"
                     («term_*_» (num "2") "*" `δ))))]
                 ":="
                 (Term.byTactic
                  "by"
                  (Tactic.tacticSeq
                   (Tactic.tacticSeq1Indented
                    [(Tactic.intro "intro" [`j])
                     []
                     (calcTactic
                      "calc"
                      (calcStep
                       («term_≤_»
                        (Term.app `dist [(Term.app `J.upper [`j]) (Term.app `J.lower [`j])])
                        "≤"
                        (Term.app `dist [`J.upper `J.lower]))
                       ":="
                       (Term.app
                        `dist_le_pi_dist
                        [(Term.hole "_") (Term.hole "_") (Term.hole "_")]))
                      [(calcStep
                        («term_≤_»
                         (Term.hole "_")
                         "≤"
                         («term_+_»
                          (Term.app `dist [`J.upper `x])
                          "+"
                          (Term.app `dist [`J.lower `x])))
                        ":="
                        (Term.app
                         `dist_triangle_right
                         [(Term.hole "_") (Term.hole "_") (Term.hole "_")]))
                       (calcStep
                        («term_≤_» (Term.hole "_") "≤" («term_+_» `δ "+" `δ))
                        ":="
                        (Term.app
                         `add_le_add
                         [(Term.app `hJδ [`J.upper_mem_Icc]) (Term.app `hJδ [`J.lower_mem_Icc])]))
                       (calcStep
                        («term_=_» (Term.hole "_") "=" («term_*_» (num "2") "*" `δ))
                        ":="
                        (Term.proj (Term.app `two_mul [`δ]) "." `symm))])]))))))
              []
              (calcTactic
               "calc"
               (calcStep
                («term_≤_»
                 (BigOperators.Algebra.BigOperators.Basic.finset.prod_univ
                  "∏"
                  (Std.ExtendedBinder.extBinders
                   (Std.ExtendedBinder.extBinder (Lean.binderIdent `j) []))
                  ", "
                  («term|___|»
                   (group "|")
                   («term_-_» (Term.app `J.upper [`j]) "-" (Term.app `J.lower [`j]))
                   (group)
                   "|"))
                 "≤"
                 (BigOperators.Algebra.BigOperators.Basic.finset.prod_univ
                  "∏"
                  (Std.ExtendedBinder.extBinders
                   (Std.ExtendedBinder.extBinder
                    (Lean.binderIdent `j)
                    [(group ":" (Term.app `Fin [(«term_+_» `n "+" (num "1"))]))]))
                  ", "
                  («term_*_» (num "2") "*" `δ)))
                ":="
                (Term.app
                 `prod_le_prod
                 [(Term.fun
                   "fun"
                   (Term.basicFun
                    [(Term.hole "_") (Term.hole "_")]
                    []
                    "=>"
                    (Term.app `abs_nonneg [(Term.hole "_")])))
                  (Term.fun "fun" (Term.basicFun [`j `hj] [] "=>" (Term.app `this [`j])))]))
               [(calcStep
                 («term_=_»
                  (Term.hole "_")
                  "="
                  («term_^_» («term_*_» (num "2") "*" `δ) "^" («term_+_» `n "+" (num "1"))))
                 ":="
                 (Term.byTactic
                  "by"
                  (Tactic.tacticSeq
                   (Tactic.tacticSeq1Indented [(Tactic.simp "simp" [] [] [] [] [])]))))])])
            []
            (tactic__
             (cdotTk (patternIgnore (token.«· » "·")))
             [(Tactic.refine'
               "refine'"
               (Term.app
                (Term.proj
                 (Term.app
                  `norm_integral_le_of_le_const
                  [(Term.fun
                    "fun"
                    (Term.basicFun
                     [`y `hy]
                     []
                     "=>"
                     (Term.app
                      `hdfδ
                      [(Term.hole "_")
                       (Term.app `Hmaps [(Term.hole "_") `Hu `hy])
                       (Term.hole "_")
                       (Term.app `Hmaps [(Term.hole "_") `Hl `hy])])))
                   (Term.hole "_")])
                 "."
                 `trans)
                [(Term.hole "_")]))
              []
              (Tactic.refine'
               "refine'"
               (Term.app
                (Term.proj
                 (Term.app
                  `mul_le_mul_of_nonneg_right
                  [(Term.hole "_") (Term.proj (Term.app `half_pos [`ε0]) "." `le)])
                 "."
                 `trans_eq)
                [(Term.app `one_mul [(Term.hole "_")])]))
              []
              (Tactic.rwSeq
               "rw"
               []
               (Tactic.rwRuleSeq
                "["
                [(Tactic.rwRule [] `box.coe_eq_pi)
                 ","
                 (Tactic.rwRule
                  []
                  (Term.app
                   `Real.volume_pi_Ioc_to_real
                   [(Term.app `box.lower_le_upper [(Term.hole "_")])]))]
                "]")
               [])
              []
              (Tactic.refine'
               "refine'"
               (Term.app
                `prod_le_one
                [(Term.fun
                  "fun"
                  (Term.basicFun
                   [(Term.hole "_") (Term.hole "_")]
                   []
                   "=>"
                   («term_<|_»
                    (Term.proj `sub_nonneg "." (fieldIdx "2"))
                    "<|"
                    (Term.app `box.lower_le_upper [(Term.hole "_") (Term.hole "_")]))))
                 (Term.fun "fun" (Term.basicFun [`j `hj] [] "=>" (Term.hole "_")))]))
              []
              (calcTactic
               "calc"
               (calcStep
                («term_≤_»
                 («term_-_»
                  (Term.app `J.upper [(Term.app `i.succ_above [`j])])
                  "-"
                  (Term.app `J.lower [(Term.app `i.succ_above [`j])]))
                 "≤"
                 (Term.app
                  `dist
                  [(Term.app `J.upper [(Term.app `i.succ_above [`j])])
                   (Term.app `J.lower [(Term.app `i.succ_above [`j])])]))
                ":="
                (Term.app `le_abs_self [(Term.hole "_")]))
               [(calcStep
                 («term_≤_» (Term.hole "_") "≤" (Term.app `dist [`J.upper `J.lower]))
                 ":="
                 (Term.app `dist_le_pi_dist [`J.upper `J.lower (Term.app `i.succ_above [`j])]))
                (calcStep
                 («term_≤_»
                  (Term.hole "_")
                  "≤"
                  («term_+_» (Term.app `dist [`J.upper `x]) "+" (Term.app `dist [`J.lower `x])))
                 ":="
                 (Term.app `dist_triangle_right [(Term.hole "_") (Term.hole "_") (Term.hole "_")]))
                (calcStep
                 («term_≤_» (Term.hole "_") "≤" («term_+_» `δ "+" `δ))
                 ":="
                 (Term.app
                  `add_le_add
                  [(Term.app `hJδ [`J.upper_mem_Icc]) (Term.app `hJδ [`J.lower_mem_Icc])]))
                (calcStep
                 («term_≤_»
                  (Term.hole "_")
                  "≤"
                  («term_+_»
                   («term_/_» (num "1") "/" (num "2"))
                   "+"
                   («term_/_» (num "1") "/" (num "2"))))
                 ":="
                 (Term.app `add_le_add [`hδ12 `hδ12]))
                (calcStep
                 («term_=_» (Term.hole "_") "=" (num "1"))
                 ":="
                 (Term.app `add_halves [(num "1")]))])])])
          []
          (tactic__
           (cdotTk (patternIgnore (token.«· » "·")))
           [(Tactic.intro "intro" [`c `x `hx `ε `ε0])
            []
            (Std.Tactic.rcases
             "rcases"
             [(Tactic.casesTarget
               []
               (Term.app `exists_pos_mul_lt [`ε0 («term_*_» (num "2") "*" `c)]))]
             ["with"
              (Std.Tactic.RCases.rcasesPatLo
               (Std.Tactic.RCases.rcasesPatMed
                [(Std.Tactic.RCases.rcasesPat.tuple
                  "⟨"
                  [(Std.Tactic.RCases.rcasesPatLo
                    (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `ε')])
                    [])
                   ","
                   (Std.Tactic.RCases.rcasesPatLo
                    (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `ε'0)])
                    [])
                   ","
                   (Std.Tactic.RCases.rcasesPatLo
                    (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `hlt)])
                    [])]
                  "⟩")])
               [])])
            []
            (Std.Tactic.rcases
             "rcases"
             [(Tactic.casesTarget
               []
               (Term.app
                (Term.proj
                 (Term.proj
                  (Term.app `nhds_within_has_basis [`nhds_basis_closed_ball (Term.hole "_")])
                  "."
                  `mem_iff)
                 "."
                 (fieldIdx "1"))
                [(Term.app (Term.proj (Term.app `Hd [`x `hx]) "." `def) [`ε'0])]))]
             ["with"
              (Std.Tactic.RCases.rcasesPatLo
               (Std.Tactic.RCases.rcasesPatMed
                [(Std.Tactic.RCases.rcasesPat.tuple
                  "⟨"
                  [(Std.Tactic.RCases.rcasesPatLo
                    (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `δ)])
                    [])
                   ","
                   (Std.Tactic.RCases.rcasesPatLo
                    (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `δ0)])
                    [])
                   ","
                   (Std.Tactic.RCases.rcasesPatLo
                    (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `Hδ)])
                    [])]
                  "⟩")])
               [])])
            []
            (Tactic.refine'
             "refine'"
             (Term.anonymousCtor
              "⟨"
              [`δ
               ","
               `δ0
               ","
               (Term.fun "fun" (Term.basicFun [`J `hle `hJδ `hxJ `hJc] [] "=>" (Term.hole "_")))]
              "⟩"))
            []
            (Tactic.simp
             "simp"
             []
             []
             ["only"]
             ["["
              [(Tactic.simpLemma [] [] `box_additive_map.volume_apply)
               ","
               (Tactic.simpLemma [] [] `box.volume_apply)
               ","
               (Tactic.simpLemma [] [] `dist_eq_norm)]
              "]"]
             [])
            []
            (Tactic.refine'
             "refine'"
             (Term.app
              (Term.proj
               (Term.app
                `norm_volume_sub_integral_face_upper_sub_lower_smul_le
                [(Term.hole "_")
                 («term_<|_»
                  `Hc.mono
                  "<|"
                  (Term.app (Term.proj `box.le_iff_Icc "." (fieldIdx "1")) [`hle]))
                 `hxJ
                 `ε'0
                 (Term.fun "fun" (Term.basicFun [`y `hy] [] "=>" (Term.app `Hδ [(Term.hole "_")])))
                 (Term.app `hJc [`rfl])])
               "."
               `trans)
              [(Term.hole "_")]))
            []
            (tactic__
             (cdotTk (patternIgnore (token.«· » "·")))
             [(Tactic.exact
               "exact"
               (Term.anonymousCtor
                "⟨"
                [(Term.app `hJδ [`hy])
                 ","
                 (Term.app (Term.proj `box.le_iff_Icc "." (fieldIdx "1")) [`hle `hy])]
                "⟩"))])
            []
            (tactic__
             (cdotTk (patternIgnore (token.«· » "·")))
             [(Tactic.rwSeq
               "rw"
               []
               (Tactic.rwRuleSeq
                "["
                [(Tactic.rwRule
                  []
                  (Term.app
                   `mul_right_comm
                   [(Term.typeAscription "(" (num "2") ":" [(Data.Real.Basic.termℝ "ℝ")] ")")]))
                 ","
                 (Tactic.rwRule [(patternIgnore (token.«← » "←"))] `box.volume_apply)]
                "]")
               [])
              []
              (Tactic.exact
               "exact"
               (Term.app `mul_le_mul_of_nonneg_right [`hlt.le `Ennreal.to_real_nonneg]))])])])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (tactic__
       (cdotTk (patternIgnore (token.«· » "·")))
       [(Tactic.intro "intro" [`c `x `hx `ε `ε0])
        []
        (Std.Tactic.rcases
         "rcases"
         [(Tactic.casesTarget [] (Term.app `exists_pos_mul_lt [`ε0 («term_*_» (num "2") "*" `c)]))]
         ["with"
          (Std.Tactic.RCases.rcasesPatLo
           (Std.Tactic.RCases.rcasesPatMed
            [(Std.Tactic.RCases.rcasesPat.tuple
              "⟨"
              [(Std.Tactic.RCases.rcasesPatLo
                (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `ε')])
                [])
               ","
               (Std.Tactic.RCases.rcasesPatLo
                (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `ε'0)])
                [])
               ","
               (Std.Tactic.RCases.rcasesPatLo
                (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `hlt)])
                [])]
              "⟩")])
           [])])
        []
        (Std.Tactic.rcases
         "rcases"
         [(Tactic.casesTarget
           []
           (Term.app
            (Term.proj
             (Term.proj
              (Term.app `nhds_within_has_basis [`nhds_basis_closed_ball (Term.hole "_")])
              "."
              `mem_iff)
             "."
             (fieldIdx "1"))
            [(Term.app (Term.proj (Term.app `Hd [`x `hx]) "." `def) [`ε'0])]))]
         ["with"
          (Std.Tactic.RCases.rcasesPatLo
           (Std.Tactic.RCases.rcasesPatMed
            [(Std.Tactic.RCases.rcasesPat.tuple
              "⟨"
              [(Std.Tactic.RCases.rcasesPatLo
                (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `δ)])
                [])
               ","
               (Std.Tactic.RCases.rcasesPatLo
                (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `δ0)])
                [])
               ","
               (Std.Tactic.RCases.rcasesPatLo
                (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `Hδ)])
                [])]
              "⟩")])
           [])])
        []
        (Tactic.refine'
         "refine'"
         (Term.anonymousCtor
          "⟨"
          [`δ
           ","
           `δ0
           ","
           (Term.fun "fun" (Term.basicFun [`J `hle `hJδ `hxJ `hJc] [] "=>" (Term.hole "_")))]
          "⟩"))
        []
        (Tactic.simp
         "simp"
         []
         []
         ["only"]
         ["["
          [(Tactic.simpLemma [] [] `box_additive_map.volume_apply)
           ","
           (Tactic.simpLemma [] [] `box.volume_apply)
           ","
           (Tactic.simpLemma [] [] `dist_eq_norm)]
          "]"]
         [])
        []
        (Tactic.refine'
         "refine'"
         (Term.app
          (Term.proj
           (Term.app
            `norm_volume_sub_integral_face_upper_sub_lower_smul_le
            [(Term.hole "_")
             («term_<|_»
              `Hc.mono
              "<|"
              (Term.app (Term.proj `box.le_iff_Icc "." (fieldIdx "1")) [`hle]))
             `hxJ
             `ε'0
             (Term.fun "fun" (Term.basicFun [`y `hy] [] "=>" (Term.app `Hδ [(Term.hole "_")])))
             (Term.app `hJc [`rfl])])
           "."
           `trans)
          [(Term.hole "_")]))
        []
        (tactic__
         (cdotTk (patternIgnore (token.«· » "·")))
         [(Tactic.exact
           "exact"
           (Term.anonymousCtor
            "⟨"
            [(Term.app `hJδ [`hy])
             ","
             (Term.app (Term.proj `box.le_iff_Icc "." (fieldIdx "1")) [`hle `hy])]
            "⟩"))])
        []
        (tactic__
         (cdotTk (patternIgnore (token.«· » "·")))
         [(Tactic.rwSeq
           "rw"
           []
           (Tactic.rwRuleSeq
            "["
            [(Tactic.rwRule
              []
              (Term.app
               `mul_right_comm
               [(Term.typeAscription "(" (num "2") ":" [(Data.Real.Basic.termℝ "ℝ")] ")")]))
             ","
             (Tactic.rwRule [(patternIgnore (token.«← » "←"))] `box.volume_apply)]
            "]")
           [])
          []
          (Tactic.exact
           "exact"
           (Term.app `mul_le_mul_of_nonneg_right [`hlt.le `Ennreal.to_real_nonneg]))])])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (tactic__
       (cdotTk (patternIgnore (token.«· » "·")))
       [(Tactic.rwSeq
         "rw"
         []
         (Tactic.rwRuleSeq
          "["
          [(Tactic.rwRule
            []
            (Term.app
             `mul_right_comm
             [(Term.typeAscription "(" (num "2") ":" [(Data.Real.Basic.termℝ "ℝ")] ")")]))
           ","
           (Tactic.rwRule [(patternIgnore (token.«← » "←"))] `box.volume_apply)]
          "]")
         [])
        []
        (Tactic.exact
         "exact"
         (Term.app `mul_le_mul_of_nonneg_right [`hlt.le `Ennreal.to_real_nonneg]))])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.exact
       "exact"
       (Term.app `mul_le_mul_of_nonneg_right [`hlt.le `Ennreal.to_real_nonneg]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `mul_le_mul_of_nonneg_right [`hlt.le `Ennreal.to_real_nonneg])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `Ennreal.to_real_nonneg
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `hlt.le
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `mul_le_mul_of_nonneg_right
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
        [(Tactic.rwRule
          []
          (Term.app
           `mul_right_comm
           [(Term.typeAscription "(" (num "2") ":" [(Data.Real.Basic.termℝ "ℝ")] ")")]))
         ","
         (Tactic.rwRule [(patternIgnore (token.«← » "←"))] `box.volume_apply)]
        "]")
       [])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `box.volume_apply
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       `mul_right_comm
       [(Term.typeAscription "(" (num "2") ":" [(Data.Real.Basic.termℝ "ℝ")] ")")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.typeAscription', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.typeAscription', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.typeAscription "(" (num "2") ":" [(Data.Real.Basic.termℝ "ℝ")] ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Data.Real.Basic.termℝ "ℝ")
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (num "2")
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `mul_right_comm
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (tactic__
       (cdotTk (patternIgnore (token.«· » "·")))
       [(Tactic.exact
         "exact"
         (Term.anonymousCtor
          "⟨"
          [(Term.app `hJδ [`hy])
           ","
           (Term.app (Term.proj `box.le_iff_Icc "." (fieldIdx "1")) [`hle `hy])]
          "⟩"))])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.exact
       "exact"
       (Term.anonymousCtor
        "⟨"
        [(Term.app `hJδ [`hy])
         ","
         (Term.app (Term.proj `box.le_iff_Icc "." (fieldIdx "1")) [`hle `hy])]
        "⟩"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.anonymousCtor
       "⟨"
       [(Term.app `hJδ [`hy])
        ","
        (Term.app (Term.proj `box.le_iff_Icc "." (fieldIdx "1")) [`hle `hy])]
       "⟩")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app (Term.proj `box.le_iff_Icc "." (fieldIdx "1")) [`hle `hy])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `hy
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `hle
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (Term.proj `box.le_iff_Icc "." (fieldIdx "1"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `box.le_iff_Icc
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `hJδ [`hy])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `hy
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `hJδ
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.refine'
       "refine'"
       (Term.app
        (Term.proj
         (Term.app
          `norm_volume_sub_integral_face_upper_sub_lower_smul_le
          [(Term.hole "_")
           («term_<|_»
            `Hc.mono
            "<|"
            (Term.app (Term.proj `box.le_iff_Icc "." (fieldIdx "1")) [`hle]))
           `hxJ
           `ε'0
           (Term.fun "fun" (Term.basicFun [`y `hy] [] "=>" (Term.app `Hδ [(Term.hole "_")])))
           (Term.app `hJc [`rfl])])
         "."
         `trans)
        [(Term.hole "_")]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       (Term.proj
        (Term.app
         `norm_volume_sub_integral_face_upper_sub_lower_smul_le
         [(Term.hole "_")
          («term_<|_»
           `Hc.mono
           "<|"
           (Term.app (Term.proj `box.le_iff_Icc "." (fieldIdx "1")) [`hle]))
          `hxJ
          `ε'0
          (Term.fun "fun" (Term.basicFun [`y `hy] [] "=>" (Term.app `Hδ [(Term.hole "_")])))
          (Term.app `hJc [`rfl])])
        "."
        `trans)
       [(Term.hole "_")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (Term.proj
       (Term.app
        `norm_volume_sub_integral_face_upper_sub_lower_smul_le
        [(Term.hole "_")
         («term_<|_» `Hc.mono "<|" (Term.app (Term.proj `box.le_iff_Icc "." (fieldIdx "1")) [`hle]))
         `hxJ
         `ε'0
         (Term.fun "fun" (Term.basicFun [`y `hy] [] "=>" (Term.app `Hδ [(Term.hole "_")])))
         (Term.app `hJc [`rfl])])
       "."
       `trans)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.app
       `norm_volume_sub_integral_face_upper_sub_lower_smul_le
       [(Term.hole "_")
        («term_<|_» `Hc.mono "<|" (Term.app (Term.proj `box.le_iff_Icc "." (fieldIdx "1")) [`hle]))
        `hxJ
        `ε'0
        (Term.fun "fun" (Term.basicFun [`y `hy] [] "=>" (Term.app `Hδ [(Term.hole "_")])))
        (Term.app `hJc [`rfl])])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `hJc [`rfl])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `rfl
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `hJc
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren "(" (Term.app `hJc [`rfl]) ")")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.fun "fun" (Term.basicFun [`y `hy] [] "=>" (Term.app `Hδ [(Term.hole "_")])))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `Hδ [(Term.hole "_")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `Hδ
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.strictImplicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.implicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.instBinder'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `hy
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.strictImplicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.implicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.instBinder'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `y
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (some 0, term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.fun "fun" (Term.basicFun [`y `hy] [] "=>" (Term.app `Hδ [(Term.hole "_")])))
     ")")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `ε'0
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `hxJ
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_<|_»', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_<|_»', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      («term_<|_» `Hc.mono "<|" (Term.app (Term.proj `box.le_iff_Icc "." (fieldIdx "1")) [`hle]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app (Term.proj `box.le_iff_Icc "." (fieldIdx "1")) [`hle])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `hle
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (Term.proj `box.le_iff_Icc "." (fieldIdx "1"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `box.le_iff_Icc
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 10 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 10, term))
      `Hc.mono
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 10, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 10, (some 10, term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     («term_<|_» `Hc.mono "<|" (Term.app (Term.proj `box.le_iff_Icc "." (fieldIdx "1")) [`hle]))
     ")")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `norm_volume_sub_integral_face_upper_sub_lower_smul_le
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.app
      `norm_volume_sub_integral_face_upper_sub_lower_smul_le
      [(Term.hole "_")
       (Term.paren
        "("
        («term_<|_» `Hc.mono "<|" (Term.app (Term.proj `box.le_iff_Icc "." (fieldIdx "1")) [`hle]))
        ")")
       `hxJ
       `ε'0
       (Term.paren
        "("
        (Term.fun "fun" (Term.basicFun [`y `hy] [] "=>" (Term.app `Hδ [(Term.hole "_")])))
        ")")
       (Term.paren "(" (Term.app `hJc [`rfl]) ")")])
     ")")
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
        [(Tactic.simpLemma [] [] `box_additive_map.volume_apply)
         ","
         (Tactic.simpLemma [] [] `box.volume_apply)
         ","
         (Tactic.simpLemma [] [] `dist_eq_norm)]
        "]"]
       [])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `dist_eq_norm
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `box.volume_apply
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `box_additive_map.volume_apply
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.refine'
       "refine'"
       (Term.anonymousCtor
        "⟨"
        [`δ
         ","
         `δ0
         ","
         (Term.fun "fun" (Term.basicFun [`J `hle `hJδ `hxJ `hJc] [] "=>" (Term.hole "_")))]
        "⟩"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.anonymousCtor
       "⟨"
       [`δ
        ","
        `δ0
        ","
        (Term.fun "fun" (Term.basicFun [`J `hle `hJδ `hxJ `hJc] [] "=>" (Term.hole "_")))]
       "⟩")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.fun "fun" (Term.basicFun [`J `hle `hJδ `hxJ `hJc] [] "=>" (Term.hole "_")))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.strictImplicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.implicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.instBinder'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `hJc
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.strictImplicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.implicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.instBinder'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `hxJ
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.strictImplicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.implicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.instBinder'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `hJδ
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.strictImplicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.implicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.instBinder'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `hle
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.strictImplicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.implicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.instBinder'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `J
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `δ0
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `δ
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Std.Tactic.rcases
       "rcases"
       [(Tactic.casesTarget
         []
         (Term.app
          (Term.proj
           (Term.proj
            (Term.app `nhds_within_has_basis [`nhds_basis_closed_ball (Term.hole "_")])
            "."
            `mem_iff)
           "."
           (fieldIdx "1"))
          [(Term.app (Term.proj (Term.app `Hd [`x `hx]) "." `def) [`ε'0])]))]
       ["with"
        (Std.Tactic.RCases.rcasesPatLo
         (Std.Tactic.RCases.rcasesPatMed
          [(Std.Tactic.RCases.rcasesPat.tuple
            "⟨"
            [(Std.Tactic.RCases.rcasesPatLo
              (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `δ)])
              [])
             ","
             (Std.Tactic.RCases.rcasesPatLo
              (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `δ0)])
              [])
             ","
             (Std.Tactic.RCases.rcasesPatLo
              (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `Hδ)])
              [])]
            "⟩")])
         [])])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       (Term.proj
        (Term.proj
         (Term.app `nhds_within_has_basis [`nhds_basis_closed_ball (Term.hole "_")])
         "."
         `mem_iff)
        "."
        (fieldIdx "1"))
       [(Term.app (Term.proj (Term.app `Hd [`x `hx]) "." `def) [`ε'0])])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app (Term.proj (Term.app `Hd [`x `hx]) "." `def) [`ε'0])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `ε'0
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (Term.proj (Term.app `Hd [`x `hx]) "." `def)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.app `Hd [`x `hx])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `hx
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `x
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `Hd
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren "(" (Term.app `Hd [`x `hx]) ")")
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.app (Term.proj (Term.paren "(" (Term.app `Hd [`x `hx]) ")") "." `def) [`ε'0])
     ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (Term.proj
       (Term.proj
        (Term.app `nhds_within_has_basis [`nhds_basis_closed_ball (Term.hole "_")])
        "."
        `mem_iff)
       "."
       (fieldIdx "1"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.proj
       (Term.app `nhds_within_has_basis [`nhds_basis_closed_ball (Term.hole "_")])
       "."
       `mem_iff)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.app `nhds_within_has_basis [`nhds_basis_closed_ball (Term.hole "_")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, term))
      `nhds_basis_closed_ball
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1023, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `nhds_within_has_basis
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.app `nhds_within_has_basis [`nhds_basis_closed_ball (Term.hole "_")])
     ")")
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Std.Tactic.rcases
       "rcases"
       [(Tactic.casesTarget [] (Term.app `exists_pos_mul_lt [`ε0 («term_*_» (num "2") "*" `c)]))]
       ["with"
        (Std.Tactic.RCases.rcasesPatLo
         (Std.Tactic.RCases.rcasesPatMed
          [(Std.Tactic.RCases.rcasesPat.tuple
            "⟨"
            [(Std.Tactic.RCases.rcasesPatLo
              (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `ε')])
              [])
             ","
             (Std.Tactic.RCases.rcasesPatLo
              (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `ε'0)])
              [])
             ","
             (Std.Tactic.RCases.rcasesPatLo
              (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `hlt)])
              [])]
            "⟩")])
         [])])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `exists_pos_mul_lt [`ε0 («term_*_» (num "2") "*" `c)])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_*_»', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_*_»', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_*_» (num "2") "*" `c)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `c
[PrettyPrinter.parenthesize] ...precedences are 71 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 70, term))
      (num "2")
[PrettyPrinter.parenthesize] ...precedences are 70 >? 1024, (none, [anonymous]) <=? (some 70, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 70, (some 71, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren "(" («term_*_» (num "2") "*" `c) ")")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `ε0
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `exists_pos_mul_lt
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.intro "intro" [`c `x `hx `ε `ε0])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `ε0
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `ε
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `hx
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `x
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `c
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (tactic__
       (cdotTk (patternIgnore (token.«· » "·")))
       [(Tactic.intro "intro" [`c `x `hx `ε `ε0])
        []
        (Tactic.tacticHave_
         "have"
         (Term.haveDecl
          (Term.haveIdDecl
           []
           [(Term.typeSpec
             ":"
             (Filter.Order.Filter.Basic.«term∀ᶠ_in_,_»
              "∀ᶠ"
              (Std.ExtendedBinder.extBinders
               (Std.ExtendedBinder.extBinder (Lean.binderIdent `δ) []))
              " in "
              (TopologicalSpace.Topology.Basic.nhds_within.gt
               "𝓝[>] "
               (Term.typeAscription "(" (num "0") ":" [(Data.Real.Basic.termℝ "ℝ")] ")"))
              ", "
              («term_∧_»
               («term_∈_»
                `δ
                "∈"
                (Term.app
                 `Ioc
                 [(Term.typeAscription "(" (num "0") ":" [(Data.Real.Basic.termℝ "ℝ")] ")")
                  («term_/_» (num "1") "/" (num "2"))]))
               "∧"
               («term_∧_»
                (Term.forall
                 "∀"
                 [(Term.explicitBinder "(" [`y₁] [] [] ")")
                  (Term.explicitBinder
                   "("
                   [(Term.hole "_")]
                   [":" («term_∈_» `y₁ "∈" («term_∩_» (Term.app `closed_ball [`x `δ]) "∩" `I.Icc))]
                   []
                   ")")
                  (Term.explicitBinder "(" [`y₂] [] [] ")")
                  (Term.explicitBinder
                   "("
                   [(Term.hole "_")]
                   [":" («term_∈_» `y₂ "∈" («term_∩_» (Term.app `closed_ball [`x `δ]) "∩" `I.Icc))]
                   []
                   ")")]
                 []
                 ","
                 («term_≤_»
                  (Analysis.Normed.Group.Basic.«term‖_‖»
                   "‖"
                   («term_-_» (Term.app `f [`y₁]) "-" (Term.app `f [`y₂]))
                   "‖")
                  "≤"
                  («term_/_» `ε "/" (num "2"))))
                "∧"
                («term_≤_»
                 («term_*_»
                  («term_^_» («term_*_» (num "2") "*" `δ) "^" («term_+_» `n "+" (num "1")))
                  "*"
                  (Analysis.Normed.Group.Basic.«term‖_‖»
                   "‖"
                   (Term.app `f' [`x (Term.app `Pi.single [`i (num "1")])])
                   "‖"))
                 "≤"
                 («term_/_» `ε "/" (num "2")))))))]
           ":="
           (Term.byTactic
            "by"
            (Tactic.tacticSeq
             (Tactic.tacticSeq1Indented
              [(Tactic.refine'
                "refine'"
                (Term.app
                 `eventually.and
                 [(Term.hole "_") (Term.app `eventually.and [(Term.hole "_") (Term.hole "_")])]))
               []
               (tactic__
                (cdotTk (patternIgnore (token.«· » "·")))
                [(Tactic.exact
                  "exact"
                  (Term.app
                   `Ioc_mem_nhds_within_Ioi
                   [(Term.anonymousCtor "⟨" [`le_rfl "," `one_half_pos] "⟩")]))])
               []
               (tactic__
                (cdotTk (patternIgnore (token.«· » "·")))
                [(Std.Tactic.rcases
                  "rcases"
                  [(Tactic.casesTarget
                    []
                    (Term.app
                     (Term.proj
                      (Term.app
                       (Term.proj
                        (Term.app `nhds_within_has_basis [`nhds_basis_closed_ball (Term.hole "_")])
                        "."
                        `tendsto_iff)
                       [`nhds_basis_closed_ball])
                      "."
                      (fieldIdx "1"))
                     [(Term.app `Hs [`x (Term.proj `hx "." (fieldIdx "2"))])
                      (Term.hole "_")
                      («term_<|_» `half_pos "<|" (Term.app `half_pos [`ε0]))]))]
                  ["with"
                   (Std.Tactic.RCases.rcasesPatLo
                    (Std.Tactic.RCases.rcasesPatMed
                     [(Std.Tactic.RCases.rcasesPat.tuple
                       "⟨"
                       [(Std.Tactic.RCases.rcasesPatLo
                         (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `δ₁)])
                         [])
                        ","
                        (Std.Tactic.RCases.rcasesPatLo
                         (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `δ₁0)])
                         [])
                        ","
                        (Std.Tactic.RCases.rcasesPatLo
                         (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `hδ₁)])
                         [])]
                       "⟩")])
                    [])])
                 []
                 (Tactic.filterUpwards
                  "filter_upwards"
                  [(Tactic.termList
                    "["
                    [(Term.app
                      `Ioc_mem_nhds_within_Ioi
                      [(Term.anonymousCtor "⟨" [`le_rfl "," `δ₁0] "⟩")])]
                    "]")]
                  ["with" [`δ `hδ `y₁ `hy₁ `y₂ `hy₂]]
                  [])
                 []
                 (Tactic.tacticHave_
                  "have"
                  (Term.haveDecl
                   (Term.haveIdDecl
                    []
                    [(Term.typeSpec
                      ":"
                      («term_⊆_»
                       («term_∩_» (Term.app `closed_ball [`x `δ]) "∩" `I.Icc)
                       "⊆"
                       («term_∩_» (Term.app `closed_ball [`x `δ₁]) "∩" `I.Icc)))]
                    ":="
                    (Term.app
                     `inter_subset_inter_left
                     [(Term.hole "_")
                      (Term.app
                       `closed_ball_subset_closed_ball
                       [(Term.proj `hδ "." (fieldIdx "2"))])]))))
                 []
                 (Tactic.rwSeq
                  "rw"
                  []
                  (Tactic.rwRuleSeq
                   "["
                   [(Tactic.rwRule [(patternIgnore (token.«← » "←"))] `dist_eq_norm)]
                   "]")
                  [])
                 []
                 (calcTactic
                  "calc"
                  (calcStep
                   («term_≤_»
                    (Term.app `dist [(Term.app `f [`y₁]) (Term.app `f [`y₂])])
                    "≤"
                    («term_+_»
                     (Term.app `dist [(Term.app `f [`y₁]) (Term.app `f [`x])])
                     "+"
                     (Term.app `dist [(Term.app `f [`y₂]) (Term.app `f [`x])])))
                   ":="
                   (Term.app
                    `dist_triangle_right
                    [(Term.hole "_") (Term.hole "_") (Term.hole "_")]))
                  [(calcStep
                    («term_≤_»
                     (Term.hole "_")
                     "≤"
                     («term_+_»
                      («term_/_» («term_/_» `ε "/" (num "2")) "/" (num "2"))
                      "+"
                      («term_/_» («term_/_» `ε "/" (num "2")) "/" (num "2"))))
                    ":="
                    (Term.app
                     `add_le_add
                     [(«term_<|_» (Term.app `hδ₁ [(Term.hole "_")]) "<|" (Term.app `this [`hy₁]))
                      («term_<|_» (Term.app `hδ₁ [(Term.hole "_")]) "<|" (Term.app `this [`hy₂]))]))
                   (calcStep
                    («term_=_» (Term.hole "_") "=" («term_/_» `ε "/" (num "2")))
                    ":="
                    (Term.app `add_halves [(Term.hole "_")]))])])
               []
               (tactic__
                (cdotTk (patternIgnore (token.«· » "·")))
                [(Tactic.tacticHave_
                  "have"
                  (Term.haveDecl
                   (Term.haveIdDecl
                    []
                    [(Term.typeSpec
                      ":"
                      (Term.app
                       `ContinuousWithinAt
                       [(Term.fun
                         "fun"
                         (Term.basicFun
                          [`δ]
                          []
                          "=>"
                          («term_*_»
                           («term_^_» («term_*_» (num "2") "*" `δ) "^" («term_+_» `n "+" (num "1")))
                           "*"
                           (Analysis.Normed.Group.Basic.«term‖_‖»
                            "‖"
                            (Term.app `f' [`x (Term.app `Pi.single [`i (num "1")])])
                            "‖"))))
                        (Term.app
                         `Ioi
                         [(Term.typeAscription
                           "("
                           (num "0")
                           ":"
                           [(Data.Real.Basic.termℝ "ℝ")]
                           ")")])
                        (num "0")]))]
                    ":="
                    (Term.app
                     (Term.proj
                      (Term.app
                       (Term.proj
                        (Term.app `continuous_within_at_id.const_mul [(Term.hole "_")])
                        "."
                        `pow)
                       [(Term.hole "_")])
                      "."
                      `mul_const)
                     [(Term.hole "_")]))))
                 []
                 (Tactic.refine'
                  "refine'"
                  (Term.app `this.eventually [(Term.app `ge_mem_nhds [(Term.hole "_")])]))
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
                   ["using" (Term.app `half_pos [`ε0])]))])]))))))
        []
        (Std.Tactic.rcases
         "rcases"
         [(Tactic.casesTarget [] `this.exists)]
         ["with"
          (Std.Tactic.RCases.rcasesPatLo
           (Std.Tactic.RCases.rcasesPatMed
            [(Std.Tactic.RCases.rcasesPat.tuple
              "⟨"
              [(Std.Tactic.RCases.rcasesPatLo
                (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `δ)])
                [])
               ","
               (Std.Tactic.RCases.rcasesPatLo
                (Std.Tactic.RCases.rcasesPatMed
                 [(Std.Tactic.RCases.rcasesPat.tuple
                   "⟨"
                   [(Std.Tactic.RCases.rcasesPatLo
                     (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `hδ0)])
                     [])
                    ","
                    (Std.Tactic.RCases.rcasesPatLo
                     (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `hδ12)])
                     [])]
                   "⟩")])
                [])
               ","
               (Std.Tactic.RCases.rcasesPatLo
                (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `hdfδ)])
                [])
               ","
               (Std.Tactic.RCases.rcasesPatLo
                (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `hδ)])
                [])]
              "⟩")])
           [])])
        []
        (Tactic.refine'
         "refine'"
         (Term.anonymousCtor
          "⟨"
          [`δ
           ","
           `hδ0
           ","
           (Term.fun
            "fun"
            (Term.basicFun
             [`J `hJI `hJδ `hxJ `hJc]
             []
             "=>"
             (Term.subst (Term.app `add_halves [`ε]) "▸" [(Term.hole "_")])))]
          "⟩"))
        []
        (Tactic.tacticHave_
         "have"
         (Term.haveDecl
          (Term.haveIdDecl
           [`Hl []]
           [(Term.typeSpec
             ":"
             («term_∈_»
              (Term.app `J.lower [`i])
              "∈"
              (Term.app `Icc [(Term.app `J.lower [`i]) (Term.app `J.upper [`i])])))]
           ":="
           (Term.app
            (Term.proj `Set.left_mem_Icc "." (fieldIdx "2"))
            [(Term.app `J.lower_le_upper [`i])]))))
        []
        (Tactic.tacticHave_
         "have"
         (Term.haveDecl
          (Term.haveIdDecl
           [`Hu []]
           [(Term.typeSpec
             ":"
             («term_∈_»
              (Term.app `J.upper [`i])
              "∈"
              (Term.app `Icc [(Term.app `J.lower [`i]) (Term.app `J.upper [`i])])))]
           ":="
           (Term.app
            (Term.proj `Set.right_mem_Icc "." (fieldIdx "2"))
            [(Term.app `J.lower_le_upper [`i])]))))
        []
        (Tactic.tacticHave_
         "have"
         (Term.haveDecl
          (Term.haveIdDecl
           [`Hi []]
           [(Term.typeSpec
             ":"
             (Std.ExtendedBinder.«term∀__,_»
              "∀"
              (Lean.binderIdent `x)
              («binderTerm∈_»
               "∈"
               (Term.app `Icc [(Term.app `J.lower [`i]) (Term.app `J.upper [`i])]))
              ","
              (Term.app
               (Term.explicitUniv `Integrable ".{" [(num "0") "," `u "," `u] "}")
               [(Term.app `J.face [`i])
                `GP
                (Term.fun
                 "fun"
                 (Term.basicFun [`y] [] "=>" (Term.app `f [(Term.app `i.insert_nth [`x `y])])))
                `box_additive_map.volume])))]
           ":="
           (Term.fun
            "fun"
            (Term.basicFun
             [`x `hx]
             []
             "=>"
             (Term.app
              `integrable_of_continuous_on
              [(Term.hole "_")
               (Term.app
                `box.continuous_on_face_Icc
                [(«term_<|_»
                  `Hc.mono
                  "<|"
                  (Term.app (Term.proj `box.le_iff_Icc "." (fieldIdx "1")) [`hJI]))
                 `hx])
               `volume]))))))
        []
        (Tactic.tacticHave_
         "have"
         (Term.haveDecl
          (Term.haveIdDecl
           [`hJδ' []]
           [(Term.typeSpec
             ":"
             («term_⊆_» `J.Icc "⊆" («term_∩_» (Term.app `closed_ball [`x `δ]) "∩" `I.Icc)))]
           ":="
           (Term.app
            `subset_inter
            [`hJδ (Term.app (Term.proj `box.le_iff_Icc "." (fieldIdx "1")) [`hJI])]))))
        []
        (Tactic.tacticHave_
         "have"
         (Term.haveDecl
          (Term.haveIdDecl
           [`Hmaps []]
           [(Term.typeSpec
             ":"
             (Std.ExtendedBinder.«term∀__,_»
              "∀"
              (Lean.binderIdent `z)
              («binderTerm∈_»
               "∈"
               (Term.app `Icc [(Term.app `J.lower [`i]) (Term.app `J.upper [`i])]))
              ","
              (Term.app
               `maps_to
               [(Term.app `i.insert_nth [`z])
                (Term.proj (Term.app `J.face [`i]) "." `IccCat)
                («term_∩_» (Term.app `closed_ball [`x `δ]) "∩" `I.Icc)])))]
           ":="
           (Term.fun
            "fun"
            (Term.basicFun
             [`z `hz]
             []
             "=>"
             (Term.app
              (Term.proj (Term.app `J.maps_to_insert_nth_face_Icc [`hz]) "." `mono)
              [`subset.rfl `hJδ']))))))
        []
        (Tactic.simp
         "simp"
         []
         []
         ["only"]
         ["["
          [(Tactic.simpLemma [] [] `dist_eq_norm)
           ","
           (Tactic.simpLemma [] [] `F)
           ","
           (Tactic.simpLemma [] [] `fI)]
          "]"]
         [])
        []
        (Tactic.dsimp "dsimp" [] [] [] [] [])
        []
        (Tactic.rwSeq
         "rw"
         []
         (Tactic.rwRuleSeq
          "["
          [(Tactic.rwRule
            [(patternIgnore (token.«← » "←"))]
            (Term.app
             `integral_sub
             [(Term.app `Hi [(Term.hole "_") `Hu]) (Term.app `Hi [(Term.hole "_") `Hl])]))]
          "]")
         [])
        []
        (Tactic.refine'
         "refine'"
         (Term.app
          (Term.proj (Term.app `norm_sub_le [(Term.hole "_") (Term.hole "_")]) "." `trans)
          [(Term.app `add_le_add [(Term.hole "_") (Term.hole "_")])]))
        []
        (tactic__
         (cdotTk (patternIgnore (token.«· » "·")))
         [(Mathlib.Tactic.tacticSimp_rw__
           "simp_rw"
           (Tactic.rwRuleSeq
            "["
            [(Tactic.rwRule [] `box_additive_map.volume_apply)
             ","
             (Tactic.rwRule [] `norm_smul)
             ","
             (Tactic.rwRule [] `Real.norm_eq_abs)
             ","
             (Tactic.rwRule [] `abs_prod)]
            "]")
           [])
          []
          (Tactic.refine'
           "refine'"
           (Term.app
            (Term.proj
             («term_<|_»
              (Term.app `mul_le_mul_of_nonneg_right [(Term.hole "_")])
              "<|"
              (Term.app `norm_nonneg [(Term.hole "_")]))
             "."
             `trans)
            [`hδ]))
          []
          (Tactic.tacticHave_
           "have"
           (Term.haveDecl
            (Term.haveIdDecl
             []
             [(Term.typeSpec
               ":"
               (Term.forall
                "∀"
                [`j]
                []
                ","
                («term_≤_»
                 («term|___|»
                  (group "|")
                  («term_-_» (Term.app `J.upper [`j]) "-" (Term.app `J.lower [`j]))
                  (group)
                  "|")
                 "≤"
                 («term_*_» (num "2") "*" `δ))))]
             ":="
             (Term.byTactic
              "by"
              (Tactic.tacticSeq
               (Tactic.tacticSeq1Indented
                [(Tactic.intro "intro" [`j])
                 []
                 (calcTactic
                  "calc"
                  (calcStep
                   («term_≤_»
                    (Term.app `dist [(Term.app `J.upper [`j]) (Term.app `J.lower [`j])])
                    "≤"
                    (Term.app `dist [`J.upper `J.lower]))
                   ":="
                   (Term.app `dist_le_pi_dist [(Term.hole "_") (Term.hole "_") (Term.hole "_")]))
                  [(calcStep
                    («term_≤_»
                     (Term.hole "_")
                     "≤"
                     («term_+_» (Term.app `dist [`J.upper `x]) "+" (Term.app `dist [`J.lower `x])))
                    ":="
                    (Term.app
                     `dist_triangle_right
                     [(Term.hole "_") (Term.hole "_") (Term.hole "_")]))
                   (calcStep
                    («term_≤_» (Term.hole "_") "≤" («term_+_» `δ "+" `δ))
                    ":="
                    (Term.app
                     `add_le_add
                     [(Term.app `hJδ [`J.upper_mem_Icc]) (Term.app `hJδ [`J.lower_mem_Icc])]))
                   (calcStep
                    («term_=_» (Term.hole "_") "=" («term_*_» (num "2") "*" `δ))
                    ":="
                    (Term.proj (Term.app `two_mul [`δ]) "." `symm))])]))))))
          []
          (calcTactic
           "calc"
           (calcStep
            («term_≤_»
             (BigOperators.Algebra.BigOperators.Basic.finset.prod_univ
              "∏"
              (Std.ExtendedBinder.extBinders
               (Std.ExtendedBinder.extBinder (Lean.binderIdent `j) []))
              ", "
              («term|___|»
               (group "|")
               («term_-_» (Term.app `J.upper [`j]) "-" (Term.app `J.lower [`j]))
               (group)
               "|"))
             "≤"
             (BigOperators.Algebra.BigOperators.Basic.finset.prod_univ
              "∏"
              (Std.ExtendedBinder.extBinders
               (Std.ExtendedBinder.extBinder
                (Lean.binderIdent `j)
                [(group ":" (Term.app `Fin [(«term_+_» `n "+" (num "1"))]))]))
              ", "
              («term_*_» (num "2") "*" `δ)))
            ":="
            (Term.app
             `prod_le_prod
             [(Term.fun
               "fun"
               (Term.basicFun
                [(Term.hole "_") (Term.hole "_")]
                []
                "=>"
                (Term.app `abs_nonneg [(Term.hole "_")])))
              (Term.fun "fun" (Term.basicFun [`j `hj] [] "=>" (Term.app `this [`j])))]))
           [(calcStep
             («term_=_»
              (Term.hole "_")
              "="
              («term_^_» («term_*_» (num "2") "*" `δ) "^" («term_+_» `n "+" (num "1"))))
             ":="
             (Term.byTactic
              "by"
              (Tactic.tacticSeq
               (Tactic.tacticSeq1Indented [(Tactic.simp "simp" [] [] [] [] [])]))))])])
        []
        (tactic__
         (cdotTk (patternIgnore (token.«· » "·")))
         [(Tactic.refine'
           "refine'"
           (Term.app
            (Term.proj
             (Term.app
              `norm_integral_le_of_le_const
              [(Term.fun
                "fun"
                (Term.basicFun
                 [`y `hy]
                 []
                 "=>"
                 (Term.app
                  `hdfδ
                  [(Term.hole "_")
                   (Term.app `Hmaps [(Term.hole "_") `Hu `hy])
                   (Term.hole "_")
                   (Term.app `Hmaps [(Term.hole "_") `Hl `hy])])))
               (Term.hole "_")])
             "."
             `trans)
            [(Term.hole "_")]))
          []
          (Tactic.refine'
           "refine'"
           (Term.app
            (Term.proj
             (Term.app
              `mul_le_mul_of_nonneg_right
              [(Term.hole "_") (Term.proj (Term.app `half_pos [`ε0]) "." `le)])
             "."
             `trans_eq)
            [(Term.app `one_mul [(Term.hole "_")])]))
          []
          (Tactic.rwSeq
           "rw"
           []
           (Tactic.rwRuleSeq
            "["
            [(Tactic.rwRule [] `box.coe_eq_pi)
             ","
             (Tactic.rwRule
              []
              (Term.app
               `Real.volume_pi_Ioc_to_real
               [(Term.app `box.lower_le_upper [(Term.hole "_")])]))]
            "]")
           [])
          []
          (Tactic.refine'
           "refine'"
           (Term.app
            `prod_le_one
            [(Term.fun
              "fun"
              (Term.basicFun
               [(Term.hole "_") (Term.hole "_")]
               []
               "=>"
               («term_<|_»
                (Term.proj `sub_nonneg "." (fieldIdx "2"))
                "<|"
                (Term.app `box.lower_le_upper [(Term.hole "_") (Term.hole "_")]))))
             (Term.fun "fun" (Term.basicFun [`j `hj] [] "=>" (Term.hole "_")))]))
          []
          (calcTactic
           "calc"
           (calcStep
            («term_≤_»
             («term_-_»
              (Term.app `J.upper [(Term.app `i.succ_above [`j])])
              "-"
              (Term.app `J.lower [(Term.app `i.succ_above [`j])]))
             "≤"
             (Term.app
              `dist
              [(Term.app `J.upper [(Term.app `i.succ_above [`j])])
               (Term.app `J.lower [(Term.app `i.succ_above [`j])])]))
            ":="
            (Term.app `le_abs_self [(Term.hole "_")]))
           [(calcStep
             («term_≤_» (Term.hole "_") "≤" (Term.app `dist [`J.upper `J.lower]))
             ":="
             (Term.app `dist_le_pi_dist [`J.upper `J.lower (Term.app `i.succ_above [`j])]))
            (calcStep
             («term_≤_»
              (Term.hole "_")
              "≤"
              («term_+_» (Term.app `dist [`J.upper `x]) "+" (Term.app `dist [`J.lower `x])))
             ":="
             (Term.app `dist_triangle_right [(Term.hole "_") (Term.hole "_") (Term.hole "_")]))
            (calcStep
             («term_≤_» (Term.hole "_") "≤" («term_+_» `δ "+" `δ))
             ":="
             (Term.app
              `add_le_add
              [(Term.app `hJδ [`J.upper_mem_Icc]) (Term.app `hJδ [`J.lower_mem_Icc])]))
            (calcStep
             («term_≤_»
              (Term.hole "_")
              "≤"
              («term_+_»
               («term_/_» (num "1") "/" (num "2"))
               "+"
               («term_/_» (num "1") "/" (num "2"))))
             ":="
             (Term.app `add_le_add [`hδ12 `hδ12]))
            (calcStep
             («term_=_» (Term.hole "_") "=" (num "1"))
             ":="
             (Term.app `add_halves [(num "1")]))])])])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (tactic__
       (cdotTk (patternIgnore (token.«· » "·")))
       [(Tactic.refine'
         "refine'"
         (Term.app
          (Term.proj
           (Term.app
            `norm_integral_le_of_le_const
            [(Term.fun
              "fun"
              (Term.basicFun
               [`y `hy]
               []
               "=>"
               (Term.app
                `hdfδ
                [(Term.hole "_")
                 (Term.app `Hmaps [(Term.hole "_") `Hu `hy])
                 (Term.hole "_")
                 (Term.app `Hmaps [(Term.hole "_") `Hl `hy])])))
             (Term.hole "_")])
           "."
           `trans)
          [(Term.hole "_")]))
        []
        (Tactic.refine'
         "refine'"
         (Term.app
          (Term.proj
           (Term.app
            `mul_le_mul_of_nonneg_right
            [(Term.hole "_") (Term.proj (Term.app `half_pos [`ε0]) "." `le)])
           "."
           `trans_eq)
          [(Term.app `one_mul [(Term.hole "_")])]))
        []
        (Tactic.rwSeq
         "rw"
         []
         (Tactic.rwRuleSeq
          "["
          [(Tactic.rwRule [] `box.coe_eq_pi)
           ","
           (Tactic.rwRule
            []
            (Term.app
             `Real.volume_pi_Ioc_to_real
             [(Term.app `box.lower_le_upper [(Term.hole "_")])]))]
          "]")
         [])
        []
        (Tactic.refine'
         "refine'"
         (Term.app
          `prod_le_one
          [(Term.fun
            "fun"
            (Term.basicFun
             [(Term.hole "_") (Term.hole "_")]
             []
             "=>"
             («term_<|_»
              (Term.proj `sub_nonneg "." (fieldIdx "2"))
              "<|"
              (Term.app `box.lower_le_upper [(Term.hole "_") (Term.hole "_")]))))
           (Term.fun "fun" (Term.basicFun [`j `hj] [] "=>" (Term.hole "_")))]))
        []
        (calcTactic
         "calc"
         (calcStep
          («term_≤_»
           («term_-_»
            (Term.app `J.upper [(Term.app `i.succ_above [`j])])
            "-"
            (Term.app `J.lower [(Term.app `i.succ_above [`j])]))
           "≤"
           (Term.app
            `dist
            [(Term.app `J.upper [(Term.app `i.succ_above [`j])])
             (Term.app `J.lower [(Term.app `i.succ_above [`j])])]))
          ":="
          (Term.app `le_abs_self [(Term.hole "_")]))
         [(calcStep
           («term_≤_» (Term.hole "_") "≤" (Term.app `dist [`J.upper `J.lower]))
           ":="
           (Term.app `dist_le_pi_dist [`J.upper `J.lower (Term.app `i.succ_above [`j])]))
          (calcStep
           («term_≤_»
            (Term.hole "_")
            "≤"
            («term_+_» (Term.app `dist [`J.upper `x]) "+" (Term.app `dist [`J.lower `x])))
           ":="
           (Term.app `dist_triangle_right [(Term.hole "_") (Term.hole "_") (Term.hole "_")]))
          (calcStep
           («term_≤_» (Term.hole "_") "≤" («term_+_» `δ "+" `δ))
           ":="
           (Term.app
            `add_le_add
            [(Term.app `hJδ [`J.upper_mem_Icc]) (Term.app `hJδ [`J.lower_mem_Icc])]))
          (calcStep
           («term_≤_»
            (Term.hole "_")
            "≤"
            («term_+_» («term_/_» (num "1") "/" (num "2")) "+" («term_/_» (num "1") "/" (num "2"))))
           ":="
           (Term.app `add_le_add [`hδ12 `hδ12]))
          (calcStep
           («term_=_» (Term.hole "_") "=" (num "1"))
           ":="
           (Term.app `add_halves [(num "1")]))])])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (calcTactic
       "calc"
       (calcStep
        («term_≤_»
         («term_-_»
          (Term.app `J.upper [(Term.app `i.succ_above [`j])])
          "-"
          (Term.app `J.lower [(Term.app `i.succ_above [`j])]))
         "≤"
         (Term.app
          `dist
          [(Term.app `J.upper [(Term.app `i.succ_above [`j])])
           (Term.app `J.lower [(Term.app `i.succ_above [`j])])]))
        ":="
        (Term.app `le_abs_self [(Term.hole "_")]))
       [(calcStep
         («term_≤_» (Term.hole "_") "≤" (Term.app `dist [`J.upper `J.lower]))
         ":="
         (Term.app `dist_le_pi_dist [`J.upper `J.lower (Term.app `i.succ_above [`j])]))
        (calcStep
         («term_≤_»
          (Term.hole "_")
          "≤"
          («term_+_» (Term.app `dist [`J.upper `x]) "+" (Term.app `dist [`J.lower `x])))
         ":="
         (Term.app `dist_triangle_right [(Term.hole "_") (Term.hole "_") (Term.hole "_")]))
        (calcStep
         («term_≤_» (Term.hole "_") "≤" («term_+_» `δ "+" `δ))
         ":="
         (Term.app
          `add_le_add
          [(Term.app `hJδ [`J.upper_mem_Icc]) (Term.app `hJδ [`J.lower_mem_Icc])]))
        (calcStep
         («term_≤_»
          (Term.hole "_")
          "≤"
          («term_+_» («term_/_» (num "1") "/" (num "2")) "+" («term_/_» (num "1") "/" (num "2"))))
         ":="
         (Term.app `add_le_add [`hδ12 `hδ12]))
        (calcStep
         («term_=_» (Term.hole "_") "=" (num "1"))
         ":="
         (Term.app `add_halves [(num "1")]))])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `add_halves [(num "1")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'num', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'num', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (num "1")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `add_halves
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_=_» (Term.hole "_") "=" (num "1"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (num "1")
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 50, term))
      (Term.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1024, (none, [anonymous]) <=? (some 50, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 50, (some 51, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, term))
      (Term.app `add_le_add [`hδ12 `hδ12])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `hδ12
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `hδ12
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
       («term_+_» («term_/_» (num "1") "/" (num "2")) "+" («term_/_» (num "1") "/" (num "2"))))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_+_» («term_/_» (num "1") "/" (num "2")) "+" («term_/_» (num "1") "/" (num "2")))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_/_» (num "1") "/" (num "2"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (num "2")
[PrettyPrinter.parenthesize] ...precedences are 71 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 70, term))
      (num "1")
[PrettyPrinter.parenthesize] ...precedences are 70 >? 1024, (none, [anonymous]) <=? (some 70, term)
[PrettyPrinter.parenthesize] ...precedences are 66 >? 70, (some 71, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 65, term))
      («term_/_» (num "1") "/" (num "2"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (num "2")
[PrettyPrinter.parenthesize] ...precedences are 71 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
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
      (Term.app `add_le_add [(Term.app `hJδ [`J.upper_mem_Icc]) (Term.app `hJδ [`J.lower_mem_Icc])])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `hJδ [`J.lower_mem_Icc])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `J.lower_mem_Icc
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `hJδ
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren "(" (Term.app `hJδ [`J.lower_mem_Icc]) ")")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.app `hJδ [`J.upper_mem_Icc])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `J.upper_mem_Icc
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `hJδ
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023,
     term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren "(" (Term.app `hJδ [`J.upper_mem_Icc]) ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `add_le_add
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_≤_» (Term.hole "_") "≤" («term_+_» `δ "+" `δ))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_+_» `δ "+" `δ)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `δ
[PrettyPrinter.parenthesize] ...precedences are 66 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 65, term))
      `δ
[PrettyPrinter.parenthesize] ...precedences are 65 >? 1024, (none, [anonymous]) <=? (some 65, term)
[PrettyPrinter.parenthesize] ...precedences are 51 >? 65, (some 66, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 50, term))
      (Term.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1024, (none, [anonymous]) <=? (some 50, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 50, (some 51, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, term))
      (Term.app `dist_triangle_right [(Term.hole "_") (Term.hole "_") (Term.hole "_")])
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
      `dist_triangle_right
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_≤_»
       (Term.hole "_")
       "≤"
       («term_+_» (Term.app `dist [`J.upper `x]) "+" (Term.app `dist [`J.lower `x])))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_+_» (Term.app `dist [`J.upper `x]) "+" (Term.app `dist [`J.lower `x]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `dist [`J.lower `x])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `x
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `J.lower
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `dist
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 66 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 65, term))
      (Term.app `dist [`J.upper `x])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `x
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `J.upper
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `dist
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 65 >? 1022, (some 1023, term) <=? (some 65, term)
[PrettyPrinter.parenthesize] ...precedences are 51 >? 65, (some 66, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 50, term))
      (Term.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1024, (none, [anonymous]) <=? (some 50, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 50, (some 51, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, term))
      (Term.app `dist_le_pi_dist [`J.upper `J.lower (Term.app `i.succ_above [`j])])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `i.succ_above [`j])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `j
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `i.succ_above
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren "(" (Term.app `i.succ_above [`j]) ")")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `J.lower
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `J.upper
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `dist_le_pi_dist
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_≤_» (Term.hole "_") "≤" (Term.app `dist [`J.upper `J.lower]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `dist [`J.upper `J.lower])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `J.lower
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `J.upper
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `dist
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 50, term))
      (Term.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1024, (none, [anonymous]) <=? (some 50, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 50, (some 51, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, term))
      (Term.app `le_abs_self [(Term.hole "_")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `le_abs_self
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_≤_»
       («term_-_»
        (Term.app `J.upper [(Term.app `i.succ_above [`j])])
        "-"
        (Term.app `J.lower [(Term.app `i.succ_above [`j])]))
       "≤"
       (Term.app
        `dist
        [(Term.app `J.upper [(Term.app `i.succ_above [`j])])
         (Term.app `J.lower [(Term.app `i.succ_above [`j])])]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       `dist
       [(Term.app `J.upper [(Term.app `i.succ_above [`j])])
        (Term.app `J.lower [(Term.app `i.succ_above [`j])])])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `J.lower [(Term.app `i.succ_above [`j])])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `i.succ_above [`j])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `j
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `i.succ_above
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren "(" (Term.app `i.succ_above [`j]) ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `J.lower
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.app `J.lower [(Term.paren "(" (Term.app `i.succ_above [`j]) ")")])
     ")")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.app `J.upper [(Term.app `i.succ_above [`j])])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `i.succ_above [`j])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `j
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `i.succ_above
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren "(" (Term.app `i.succ_above [`j]) ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `J.upper
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023,
     term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.app `J.upper [(Term.paren "(" (Term.app `i.succ_above [`j]) ")")])
     ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `dist
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 50, term))
      («term_-_»
       (Term.app `J.upper [(Term.app `i.succ_above [`j])])
       "-"
       (Term.app `J.lower [(Term.app `i.succ_above [`j])]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `J.lower [(Term.app `i.succ_above [`j])])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `i.succ_above [`j])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `j
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `i.succ_above
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren "(" (Term.app `i.succ_above [`j]) ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `J.lower
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 66 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 65, term))
      (Term.app `J.upper [(Term.app `i.succ_above [`j])])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `i.succ_above [`j])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `j
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `i.succ_above
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren "(" (Term.app `i.succ_above [`j]) ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `J.upper
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 65 >? 1022, (some 1023, term) <=? (some 65, term)
[PrettyPrinter.parenthesize] ...precedences are 51 >? 65, (some 66, term) <=? (some 50, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 50, (some 51, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.refine'
       "refine'"
       (Term.app
        `prod_le_one
        [(Term.fun
          "fun"
          (Term.basicFun
           [(Term.hole "_") (Term.hole "_")]
           []
           "=>"
           («term_<|_»
            (Term.proj `sub_nonneg "." (fieldIdx "2"))
            "<|"
            (Term.app `box.lower_le_upper [(Term.hole "_") (Term.hole "_")]))))
         (Term.fun "fun" (Term.basicFun [`j `hj] [] "=>" (Term.hole "_")))]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       `prod_le_one
       [(Term.fun
         "fun"
         (Term.basicFun
          [(Term.hole "_") (Term.hole "_")]
          []
          "=>"
          («term_<|_»
           (Term.proj `sub_nonneg "." (fieldIdx "2"))
           "<|"
           (Term.app `box.lower_le_upper [(Term.hole "_") (Term.hole "_")]))))
        (Term.fun "fun" (Term.basicFun [`j `hj] [] "=>" (Term.hole "_")))])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.fun "fun" (Term.basicFun [`j `hj] [] "=>" (Term.hole "_")))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.strictImplicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.implicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.instBinder'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `hj
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.strictImplicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.implicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.instBinder'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `j
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, term))
      (Term.fun
       "fun"
       (Term.basicFun
        [(Term.hole "_") (Term.hole "_")]
        []
        "=>"
        («term_<|_»
         (Term.proj `sub_nonneg "." (fieldIdx "2"))
         "<|"
         (Term.app `box.lower_le_upper [(Term.hole "_") (Term.hole "_")]))))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_<|_»
       (Term.proj `sub_nonneg "." (fieldIdx "2"))
       "<|"
       (Term.app `box.lower_le_upper [(Term.hole "_") (Term.hole "_")]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `box.lower_le_upper [(Term.hole "_") (Term.hole "_")])
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
      `box.lower_le_upper
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 10 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 10, term))
      (Term.proj `sub_nonneg "." (fieldIdx "2"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `sub_nonneg
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 10, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 10, (some 10, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.strictImplicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.implicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.instBinder'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.strictImplicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.implicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.instBinder'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, term))
      (Term.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1023, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (some 0, term) <=? (some 1023, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.fun
      "fun"
      (Term.basicFun
       [(Term.hole "_") (Term.hole "_")]
       []
       "=>"
       («term_<|_»
        (Term.proj `sub_nonneg "." (fieldIdx "2"))
        "<|"
        (Term.app `box.lower_le_upper [(Term.hole "_") (Term.hole "_")]))))
     ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `prod_le_one
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.rwSeq
       "rw"
       []
       (Tactic.rwRuleSeq
        "["
        [(Tactic.rwRule [] `box.coe_eq_pi)
         ","
         (Tactic.rwRule
          []
          (Term.app
           `Real.volume_pi_Ioc_to_real
           [(Term.app `box.lower_le_upper [(Term.hole "_")])]))]
        "]")
       [])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `Real.volume_pi_Ioc_to_real [(Term.app `box.lower_le_upper [(Term.hole "_")])])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `box.lower_le_upper [(Term.hole "_")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `box.lower_le_upper
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.app `box.lower_le_upper [(Term.hole "_")])
     ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `Real.volume_pi_Ioc_to_real
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `box.coe_eq_pi
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.refine'
       "refine'"
       (Term.app
        (Term.proj
         (Term.app
          `mul_le_mul_of_nonneg_right
          [(Term.hole "_") (Term.proj (Term.app `half_pos [`ε0]) "." `le)])
         "."
         `trans_eq)
        [(Term.app `one_mul [(Term.hole "_")])]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       (Term.proj
        (Term.app
         `mul_le_mul_of_nonneg_right
         [(Term.hole "_") (Term.proj (Term.app `half_pos [`ε0]) "." `le)])
        "."
        `trans_eq)
       [(Term.app `one_mul [(Term.hole "_")])])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `one_mul [(Term.hole "_")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `one_mul
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.app `one_mul [(Term.hole "_")])
     ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (Term.proj
       (Term.app
        `mul_le_mul_of_nonneg_right
        [(Term.hole "_") (Term.proj (Term.app `half_pos [`ε0]) "." `le)])
       "."
       `trans_eq)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.app
       `mul_le_mul_of_nonneg_right
       [(Term.hole "_") (Term.proj (Term.app `half_pos [`ε0]) "." `le)])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.proj', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.proj', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.proj (Term.app `half_pos [`ε0]) "." `le)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.app `half_pos [`ε0])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `ε0
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `half_pos
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren "(" (Term.app `half_pos [`ε0]) ")")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `mul_le_mul_of_nonneg_right
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.app
      `mul_le_mul_of_nonneg_right
      [(Term.hole "_") (Term.proj (Term.paren "(" (Term.app `half_pos [`ε0]) ")") "." `le)])
     ")")
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.refine'
       "refine'"
       (Term.app
        (Term.proj
         (Term.app
          `norm_integral_le_of_le_const
          [(Term.fun
            "fun"
            (Term.basicFun
             [`y `hy]
             []
             "=>"
             (Term.app
              `hdfδ
              [(Term.hole "_")
               (Term.app `Hmaps [(Term.hole "_") `Hu `hy])
               (Term.hole "_")
               (Term.app `Hmaps [(Term.hole "_") `Hl `hy])])))
           (Term.hole "_")])
         "."
         `trans)
        [(Term.hole "_")]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       (Term.proj
        (Term.app
         `norm_integral_le_of_le_const
         [(Term.fun
           "fun"
           (Term.basicFun
            [`y `hy]
            []
            "=>"
            (Term.app
             `hdfδ
             [(Term.hole "_")
              (Term.app `Hmaps [(Term.hole "_") `Hu `hy])
              (Term.hole "_")
              (Term.app `Hmaps [(Term.hole "_") `Hl `hy])])))
          (Term.hole "_")])
        "."
        `trans)
       [(Term.hole "_")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (Term.proj
       (Term.app
        `norm_integral_le_of_le_const
        [(Term.fun
          "fun"
          (Term.basicFun
           [`y `hy]
           []
           "=>"
           (Term.app
            `hdfδ
            [(Term.hole "_")
             (Term.app `Hmaps [(Term.hole "_") `Hu `hy])
             (Term.hole "_")
             (Term.app `Hmaps [(Term.hole "_") `Hl `hy])])))
         (Term.hole "_")])
       "."
       `trans)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.app
       `norm_integral_le_of_le_const
       [(Term.fun
         "fun"
         (Term.basicFun
          [`y `hy]
          []
          "=>"
          (Term.app
           `hdfδ
           [(Term.hole "_")
            (Term.app `Hmaps [(Term.hole "_") `Hu `hy])
            (Term.hole "_")
            (Term.app `Hmaps [(Term.hole "_") `Hl `hy])])))
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
      (Term.fun
       "fun"
       (Term.basicFun
        [`y `hy]
        []
        "=>"
        (Term.app
         `hdfδ
         [(Term.hole "_")
          (Term.app `Hmaps [(Term.hole "_") `Hu `hy])
          (Term.hole "_")
          (Term.app `Hmaps [(Term.hole "_") `Hl `hy])])))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       `hdfδ
       [(Term.hole "_")
        (Term.app `Hmaps [(Term.hole "_") `Hu `hy])
        (Term.hole "_")
        (Term.app `Hmaps [(Term.hole "_") `Hl `hy])])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `Hmaps [(Term.hole "_") `Hl `hy])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `hy
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `Hl
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `Hmaps
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.app `Hmaps [(Term.hole "_") `Hl `hy])
     ")")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, term))
      (Term.app `Hmaps [(Term.hole "_") `Hu `hy])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `hy
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `Hu
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `Hmaps
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023,
     term) <=? (some 1023, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.app `Hmaps [(Term.hole "_") `Hu `hy])
     ")")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `hdfδ
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.strictImplicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.implicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.instBinder'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `hy
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.strictImplicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.implicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.instBinder'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `y
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (some 0, term) <=? (some 1023, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.fun
      "fun"
      (Term.basicFun
       [`y `hy]
       []
       "=>"
       (Term.app
        `hdfδ
        [(Term.hole "_")
         (Term.paren "(" (Term.app `Hmaps [(Term.hole "_") `Hu `hy]) ")")
         (Term.hole "_")
         (Term.paren "(" (Term.app `Hmaps [(Term.hole "_") `Hl `hy]) ")")])))
     ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `norm_integral_le_of_le_const
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.app
      `norm_integral_le_of_le_const
      [(Term.paren
        "("
        (Term.fun
         "fun"
         (Term.basicFun
          [`y `hy]
          []
          "=>"
          (Term.app
           `hdfδ
           [(Term.hole "_")
            (Term.paren "(" (Term.app `Hmaps [(Term.hole "_") `Hu `hy]) ")")
            (Term.hole "_")
            (Term.paren "(" (Term.app `Hmaps [(Term.hole "_") `Hl `hy]) ")")])))
        ")")
       (Term.hole "_")])
     ")")
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (tactic__
       (cdotTk (patternIgnore (token.«· » "·")))
       [(Mathlib.Tactic.tacticSimp_rw__
         "simp_rw"
         (Tactic.rwRuleSeq
          "["
          [(Tactic.rwRule [] `box_additive_map.volume_apply)
           ","
           (Tactic.rwRule [] `norm_smul)
           ","
           (Tactic.rwRule [] `Real.norm_eq_abs)
           ","
           (Tactic.rwRule [] `abs_prod)]
          "]")
         [])
        []
        (Tactic.refine'
         "refine'"
         (Term.app
          (Term.proj
           («term_<|_»
            (Term.app `mul_le_mul_of_nonneg_right [(Term.hole "_")])
            "<|"
            (Term.app `norm_nonneg [(Term.hole "_")]))
           "."
           `trans)
          [`hδ]))
        []
        (Tactic.tacticHave_
         "have"
         (Term.haveDecl
          (Term.haveIdDecl
           []
           [(Term.typeSpec
             ":"
             (Term.forall
              "∀"
              [`j]
              []
              ","
              («term_≤_»
               («term|___|»
                (group "|")
                («term_-_» (Term.app `J.upper [`j]) "-" (Term.app `J.lower [`j]))
                (group)
                "|")
               "≤"
               («term_*_» (num "2") "*" `δ))))]
           ":="
           (Term.byTactic
            "by"
            (Tactic.tacticSeq
             (Tactic.tacticSeq1Indented
              [(Tactic.intro "intro" [`j])
               []
               (calcTactic
                "calc"
                (calcStep
                 («term_≤_»
                  (Term.app `dist [(Term.app `J.upper [`j]) (Term.app `J.lower [`j])])
                  "≤"
                  (Term.app `dist [`J.upper `J.lower]))
                 ":="
                 (Term.app `dist_le_pi_dist [(Term.hole "_") (Term.hole "_") (Term.hole "_")]))
                [(calcStep
                  («term_≤_»
                   (Term.hole "_")
                   "≤"
                   («term_+_» (Term.app `dist [`J.upper `x]) "+" (Term.app `dist [`J.lower `x])))
                  ":="
                  (Term.app `dist_triangle_right [(Term.hole "_") (Term.hole "_") (Term.hole "_")]))
                 (calcStep
                  («term_≤_» (Term.hole "_") "≤" («term_+_» `δ "+" `δ))
                  ":="
                  (Term.app
                   `add_le_add
                   [(Term.app `hJδ [`J.upper_mem_Icc]) (Term.app `hJδ [`J.lower_mem_Icc])]))
                 (calcStep
                  («term_=_» (Term.hole "_") "=" («term_*_» (num "2") "*" `δ))
                  ":="
                  (Term.proj (Term.app `two_mul [`δ]) "." `symm))])]))))))
        []
        (calcTactic
         "calc"
         (calcStep
          («term_≤_»
           (BigOperators.Algebra.BigOperators.Basic.finset.prod_univ
            "∏"
            (Std.ExtendedBinder.extBinders (Std.ExtendedBinder.extBinder (Lean.binderIdent `j) []))
            ", "
            («term|___|»
             (group "|")
             («term_-_» (Term.app `J.upper [`j]) "-" (Term.app `J.lower [`j]))
             (group)
             "|"))
           "≤"
           (BigOperators.Algebra.BigOperators.Basic.finset.prod_univ
            "∏"
            (Std.ExtendedBinder.extBinders
             (Std.ExtendedBinder.extBinder
              (Lean.binderIdent `j)
              [(group ":" (Term.app `Fin [(«term_+_» `n "+" (num "1"))]))]))
            ", "
            («term_*_» (num "2") "*" `δ)))
          ":="
          (Term.app
           `prod_le_prod
           [(Term.fun
             "fun"
             (Term.basicFun
              [(Term.hole "_") (Term.hole "_")]
              []
              "=>"
              (Term.app `abs_nonneg [(Term.hole "_")])))
            (Term.fun "fun" (Term.basicFun [`j `hj] [] "=>" (Term.app `this [`j])))]))
         [(calcStep
           («term_=_»
            (Term.hole "_")
            "="
            («term_^_» («term_*_» (num "2") "*" `δ) "^" («term_+_» `n "+" (num "1"))))
           ":="
           (Term.byTactic
            "by"
            (Tactic.tacticSeq
             (Tactic.tacticSeq1Indented [(Tactic.simp "simp" [] [] [] [] [])]))))])])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (calcTactic
       "calc"
       (calcStep
        («term_≤_»
         (BigOperators.Algebra.BigOperators.Basic.finset.prod_univ
          "∏"
          (Std.ExtendedBinder.extBinders (Std.ExtendedBinder.extBinder (Lean.binderIdent `j) []))
          ", "
          («term|___|»
           (group "|")
           («term_-_» (Term.app `J.upper [`j]) "-" (Term.app `J.lower [`j]))
           (group)
           "|"))
         "≤"
         (BigOperators.Algebra.BigOperators.Basic.finset.prod_univ
          "∏"
          (Std.ExtendedBinder.extBinders
           (Std.ExtendedBinder.extBinder
            (Lean.binderIdent `j)
            [(group ":" (Term.app `Fin [(«term_+_» `n "+" (num "1"))]))]))
          ", "
          («term_*_» (num "2") "*" `δ)))
        ":="
        (Term.app
         `prod_le_prod
         [(Term.fun
           "fun"
           (Term.basicFun
            [(Term.hole "_") (Term.hole "_")]
            []
            "=>"
            (Term.app `abs_nonneg [(Term.hole "_")])))
          (Term.fun "fun" (Term.basicFun [`j `hj] [] "=>" (Term.app `this [`j])))]))
       [(calcStep
         («term_=_»
          (Term.hole "_")
          "="
          («term_^_» («term_*_» (num "2") "*" `δ) "^" («term_+_» `n "+" (num "1"))))
         ":="
         (Term.byTactic
          "by"
          (Tactic.tacticSeq (Tactic.tacticSeq1Indented [(Tactic.simp "simp" [] [] [] [] [])]))))])
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
      («term_=_»
       (Term.hole "_")
       "="
       («term_^_» («term_*_» (num "2") "*" `δ) "^" («term_+_» `n "+" (num "1"))))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_^_» («term_*_» (num "2") "*" `δ) "^" («term_+_» `n "+" (num "1")))
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
      («term_*_» (num "2") "*" `δ)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `δ
[PrettyPrinter.parenthesize] ...precedences are 71 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 70, term))
      (num "2")
[PrettyPrinter.parenthesize] ...precedences are 70 >? 1024, (none, [anonymous]) <=? (some 70, term)
[PrettyPrinter.parenthesize] ...precedences are 81 >? 70, (some 71, term) <=? (some 80, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren "(" («term_*_» (num "2") "*" `δ) ")")
[PrettyPrinter.parenthesize] ...precedences are 51 >? 80, (some 80, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 50, term))
      (Term.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1024, (none, [anonymous]) <=? (some 50, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 50, (some 51, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, term))
      (Term.app
       `prod_le_prod
       [(Term.fun
         "fun"
         (Term.basicFun
          [(Term.hole "_") (Term.hole "_")]
          []
          "=>"
          (Term.app `abs_nonneg [(Term.hole "_")])))
        (Term.fun "fun" (Term.basicFun [`j `hj] [] "=>" (Term.app `this [`j])))])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.fun "fun" (Term.basicFun [`j `hj] [] "=>" (Term.app `this [`j])))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `this [`j])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `j
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `this
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.strictImplicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.implicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.instBinder'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `hj
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.strictImplicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.implicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.instBinder'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `j
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, term))
      (Term.fun
       "fun"
       (Term.basicFun
        [(Term.hole "_") (Term.hole "_")]
        []
        "=>"
        (Term.app `abs_nonneg [(Term.hole "_")])))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `abs_nonneg [(Term.hole "_")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `abs_nonneg
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.strictImplicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.implicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.instBinder'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.strictImplicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.implicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.instBinder'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, term))
      (Term.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1023, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (some 0, term) <=? (some 1023, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.fun
      "fun"
      (Term.basicFun
       [(Term.hole "_") (Term.hole "_")]
       []
       "=>"
       (Term.app `abs_nonneg [(Term.hole "_")])))
     ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `prod_le_prod
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, term) <=? (none, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_≤_»
       (BigOperators.Algebra.BigOperators.Basic.finset.prod_univ
        "∏"
        (Std.ExtendedBinder.extBinders (Std.ExtendedBinder.extBinder (Lean.binderIdent `j) []))
        ", "
        («term|___|»
         (group "|")
         («term_-_» (Term.app `J.upper [`j]) "-" (Term.app `J.lower [`j]))
         (group)
         "|"))
       "≤"
       (BigOperators.Algebra.BigOperators.Basic.finset.prod_univ
        "∏"
        (Std.ExtendedBinder.extBinders
         (Std.ExtendedBinder.extBinder
          (Lean.binderIdent `j)
          [(group ":" (Term.app `Fin [(«term_+_» `n "+" (num "1"))]))]))
        ", "
        («term_*_» (num "2") "*" `δ)))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (BigOperators.Algebra.BigOperators.Basic.finset.prod_univ
       "∏"
       (Std.ExtendedBinder.extBinders
        (Std.ExtendedBinder.extBinder
         (Lean.binderIdent `j)
         [(group ":" (Term.app `Fin [(«term_+_» `n "+" (num "1"))]))]))
       ", "
       («term_*_» (num "2") "*" `δ))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_*_» (num "2") "*" `δ)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `δ
[PrettyPrinter.parenthesize] ...precedences are 71 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 70, term))
      (num "2")
[PrettyPrinter.parenthesize] ...precedences are 70 >? 1024, (none, [anonymous]) <=? (some 70, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 70, (some 71, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `Fin [(«term_+_» `n "+" (num "1"))])
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
      `Fin
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1022, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 50, term))
      (BigOperators.Algebra.BigOperators.Basic.finset.prod_univ
       "∏"
       (Std.ExtendedBinder.extBinders (Std.ExtendedBinder.extBinder (Lean.binderIdent `j) []))
       ", "
       («term|___|»
        (group "|")
        («term_-_» (Term.app `J.upper [`j]) "-" (Term.app `J.lower [`j]))
        (group)
        "|"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term|___|»
       (group "|")
       («term_-_» (Term.app `J.upper [`j]) "-" (Term.app `J.lower [`j]))
       (group)
       "|")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_-_» (Term.app `J.upper [`j]) "-" (Term.app `J.lower [`j]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `J.lower [`j])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `j
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `J.lower
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 66 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 65, term))
      (Term.app `J.upper [`j])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `j
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `J.upper
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 65 >? 1022, (some 1023, term) <=? (some 65, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 65, (some 66, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1022, (some 0, term) <=? (some 50, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (BigOperators.Algebra.BigOperators.Basic.finset.prod_univ
      "∏"
      (Std.ExtendedBinder.extBinders (Std.ExtendedBinder.extBinder (Lean.binderIdent `j) []))
      ", "
      («term|___|»
       (group "|")
       («term_-_» (Term.app `J.upper [`j]) "-" (Term.app `J.lower [`j]))
       (group)
       "|"))
     ")")
[PrettyPrinter.parenthesize] ...precedences are 0 >? 50, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.tacticHave_
       "have"
       (Term.haveDecl
        (Term.haveIdDecl
         []
         [(Term.typeSpec
           ":"
           (Term.forall
            "∀"
            [`j]
            []
            ","
            («term_≤_»
             («term|___|»
              (group "|")
              («term_-_» (Term.app `J.upper [`j]) "-" (Term.app `J.lower [`j]))
              (group)
              "|")
             "≤"
             («term_*_» (num "2") "*" `δ))))]
         ":="
         (Term.byTactic
          "by"
          (Tactic.tacticSeq
           (Tactic.tacticSeq1Indented
            [(Tactic.intro "intro" [`j])
             []
             (calcTactic
              "calc"
              (calcStep
               («term_≤_»
                (Term.app `dist [(Term.app `J.upper [`j]) (Term.app `J.lower [`j])])
                "≤"
                (Term.app `dist [`J.upper `J.lower]))
               ":="
               (Term.app `dist_le_pi_dist [(Term.hole "_") (Term.hole "_") (Term.hole "_")]))
              [(calcStep
                («term_≤_»
                 (Term.hole "_")
                 "≤"
                 («term_+_» (Term.app `dist [`J.upper `x]) "+" (Term.app `dist [`J.lower `x])))
                ":="
                (Term.app `dist_triangle_right [(Term.hole "_") (Term.hole "_") (Term.hole "_")]))
               (calcStep
                («term_≤_» (Term.hole "_") "≤" («term_+_» `δ "+" `δ))
                ":="
                (Term.app
                 `add_le_add
                 [(Term.app `hJδ [`J.upper_mem_Icc]) (Term.app `hJδ [`J.lower_mem_Icc])]))
               (calcStep
                («term_=_» (Term.hole "_") "=" («term_*_» (num "2") "*" `δ))
                ":="
                (Term.proj (Term.app `two_mul [`δ]) "." `symm))])]))))))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.byTactic
       "by"
       (Tactic.tacticSeq
        (Tactic.tacticSeq1Indented
         [(Tactic.intro "intro" [`j])
          []
          (calcTactic
           "calc"
           (calcStep
            («term_≤_»
             (Term.app `dist [(Term.app `J.upper [`j]) (Term.app `J.lower [`j])])
             "≤"
             (Term.app `dist [`J.upper `J.lower]))
            ":="
            (Term.app `dist_le_pi_dist [(Term.hole "_") (Term.hole "_") (Term.hole "_")]))
           [(calcStep
             («term_≤_»
              (Term.hole "_")
              "≤"
              («term_+_» (Term.app `dist [`J.upper `x]) "+" (Term.app `dist [`J.lower `x])))
             ":="
             (Term.app `dist_triangle_right [(Term.hole "_") (Term.hole "_") (Term.hole "_")]))
            (calcStep
             («term_≤_» (Term.hole "_") "≤" («term_+_» `δ "+" `δ))
             ":="
             (Term.app
              `add_le_add
              [(Term.app `hJδ [`J.upper_mem_Icc]) (Term.app `hJδ [`J.lower_mem_Icc])]))
            (calcStep
             («term_=_» (Term.hole "_") "=" («term_*_» (num "2") "*" `δ))
             ":="
             (Term.proj (Term.app `two_mul [`δ]) "." `symm))])])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (calcTactic
       "calc"
       (calcStep
        («term_≤_»
         (Term.app `dist [(Term.app `J.upper [`j]) (Term.app `J.lower [`j])])
         "≤"
         (Term.app `dist [`J.upper `J.lower]))
        ":="
        (Term.app `dist_le_pi_dist [(Term.hole "_") (Term.hole "_") (Term.hole "_")]))
       [(calcStep
         («term_≤_»
          (Term.hole "_")
          "≤"
          («term_+_» (Term.app `dist [`J.upper `x]) "+" (Term.app `dist [`J.lower `x])))
         ":="
         (Term.app `dist_triangle_right [(Term.hole "_") (Term.hole "_") (Term.hole "_")]))
        (calcStep
         («term_≤_» (Term.hole "_") "≤" («term_+_» `δ "+" `δ))
         ":="
         (Term.app
          `add_le_add
          [(Term.app `hJδ [`J.upper_mem_Icc]) (Term.app `hJδ [`J.lower_mem_Icc])]))
        (calcStep
         («term_=_» (Term.hole "_") "=" («term_*_» (num "2") "*" `δ))
         ":="
         (Term.proj (Term.app `two_mul [`δ]) "." `symm))])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.proj (Term.app `two_mul [`δ]) "." `symm)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.app `two_mul [`δ])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `δ
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `two_mul
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren "(" (Term.app `two_mul [`δ]) ")")
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_=_» (Term.hole "_") "=" («term_*_» (num "2") "*" `δ))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_*_» (num "2") "*" `δ)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `δ
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
      (Term.app `add_le_add [(Term.app `hJδ [`J.upper_mem_Icc]) (Term.app `hJδ [`J.lower_mem_Icc])])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `hJδ [`J.lower_mem_Icc])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `J.lower_mem_Icc
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `hJδ
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren "(" (Term.app `hJδ [`J.lower_mem_Icc]) ")")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.app `hJδ [`J.upper_mem_Icc])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `J.upper_mem_Icc
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `hJδ
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023,
     term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren "(" (Term.app `hJδ [`J.upper_mem_Icc]) ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `add_le_add
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_≤_» (Term.hole "_") "≤" («term_+_» `δ "+" `δ))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_+_» `δ "+" `δ)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `δ
[PrettyPrinter.parenthesize] ...precedences are 66 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 65, term))
      `δ
[PrettyPrinter.parenthesize] ...precedences are 65 >? 1024, (none, [anonymous]) <=? (some 65, term)
[PrettyPrinter.parenthesize] ...precedences are 51 >? 65, (some 66, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 50, term))
      (Term.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1024, (none, [anonymous]) <=? (some 50, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 50, (some 51, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, term))
      (Term.app `dist_triangle_right [(Term.hole "_") (Term.hole "_") (Term.hole "_")])
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
      `dist_triangle_right
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_≤_»
       (Term.hole "_")
       "≤"
       («term_+_» (Term.app `dist [`J.upper `x]) "+" (Term.app `dist [`J.lower `x])))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_+_» (Term.app `dist [`J.upper `x]) "+" (Term.app `dist [`J.lower `x]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `dist [`J.lower `x])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `x
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `J.lower
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `dist
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 66 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 65, term))
      (Term.app `dist [`J.upper `x])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `x
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `J.upper
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `dist
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 65 >? 1022, (some 1023, term) <=? (some 65, term)
[PrettyPrinter.parenthesize] ...precedences are 51 >? 65, (some 66, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 50, term))
      (Term.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1024, (none, [anonymous]) <=? (some 50, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 50, (some 51, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, term))
      (Term.app `dist_le_pi_dist [(Term.hole "_") (Term.hole "_") (Term.hole "_")])
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
      `dist_le_pi_dist
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_≤_»
       (Term.app `dist [(Term.app `J.upper [`j]) (Term.app `J.lower [`j])])
       "≤"
       (Term.app `dist [`J.upper `J.lower]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `dist [`J.upper `J.lower])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `J.lower
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `J.upper
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `dist
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 50, term))
      (Term.app `dist [(Term.app `J.upper [`j]) (Term.app `J.lower [`j])])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `J.lower [`j])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `j
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `J.lower
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren "(" (Term.app `J.lower [`j]) ")")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.app `J.upper [`j])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `j
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `J.upper
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023,
     term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren "(" (Term.app `J.upper [`j]) ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `dist
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1022, (some 1023, term) <=? (some 50, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 50, (some 51, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.intro "intro" [`j])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `j
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, tactic) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.forall
       "∀"
       [`j]
       []
       ","
       («term_≤_»
        («term|___|»
         (group "|")
         («term_-_» (Term.app `J.upper [`j]) "-" (Term.app `J.lower [`j]))
         (group)
         "|")
        "≤"
        («term_*_» (num "2") "*" `δ)))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_≤_»
       («term|___|»
        (group "|")
        («term_-_» (Term.app `J.upper [`j]) "-" (Term.app `J.lower [`j]))
        (group)
        "|")
       "≤"
       («term_*_» (num "2") "*" `δ))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_*_» (num "2") "*" `δ)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `δ
[PrettyPrinter.parenthesize] ...precedences are 71 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 70, term))
      (num "2")
[PrettyPrinter.parenthesize] ...precedences are 70 >? 1024, (none, [anonymous]) <=? (some 70, term)
[PrettyPrinter.parenthesize] ...precedences are 51 >? 70, (some 71, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 50, term))
      («term|___|»
       (group "|")
       («term_-_» (Term.app `J.upper [`j]) "-" (Term.app `J.lower [`j]))
       (group)
       "|")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_-_» (Term.app `J.upper [`j]) "-" (Term.app `J.lower [`j]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `J.lower [`j])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `j
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `J.lower
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 66 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 65, term))
      (Term.app `J.upper [`j])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `j
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `J.upper
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 65 >? 1022, (some 1023, term) <=? (some 65, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 65, (some 66, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1022, (none, [anonymous]) <=? (some 50, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 50, (some 51, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.refine'
       "refine'"
       (Term.app
        (Term.proj
         («term_<|_»
          (Term.app `mul_le_mul_of_nonneg_right [(Term.hole "_")])
          "<|"
          (Term.app `norm_nonneg [(Term.hole "_")]))
         "."
         `trans)
        [`hδ]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       (Term.proj
        («term_<|_»
         (Term.app `mul_le_mul_of_nonneg_right [(Term.hole "_")])
         "<|"
         (Term.app `norm_nonneg [(Term.hole "_")]))
        "."
        `trans)
       [`hδ])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `hδ
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (Term.proj
       («term_<|_»
        (Term.app `mul_le_mul_of_nonneg_right [(Term.hole "_")])
        "<|"
        (Term.app `norm_nonneg [(Term.hole "_")]))
       "."
       `trans)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      («term_<|_»
       (Term.app `mul_le_mul_of_nonneg_right [(Term.hole "_")])
       "<|"
       (Term.app `norm_nonneg [(Term.hole "_")]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `norm_nonneg [(Term.hole "_")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `norm_nonneg
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 10 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 10, term))
      (Term.app `mul_le_mul_of_nonneg_right [(Term.hole "_")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `mul_le_mul_of_nonneg_right
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (some 10, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 10, (some 10, term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     («term_<|_»
      (Term.app `mul_le_mul_of_nonneg_right [(Term.hole "_")])
      "<|"
      (Term.app `norm_nonneg [(Term.hole "_")]))
     ")")
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Mathlib.Tactic.tacticSimp_rw__
       "simp_rw"
       (Tactic.rwRuleSeq
        "["
        [(Tactic.rwRule [] `box_additive_map.volume_apply)
         ","
         (Tactic.rwRule [] `norm_smul)
         ","
         (Tactic.rwRule [] `Real.norm_eq_abs)
         ","
         (Tactic.rwRule [] `abs_prod)]
        "]")
       [])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `abs_prod
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `Real.norm_eq_abs
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `norm_smul
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `box_additive_map.volume_apply
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.refine'
       "refine'"
       (Term.app
        (Term.proj (Term.app `norm_sub_le [(Term.hole "_") (Term.hole "_")]) "." `trans)
        [(Term.app `add_le_add [(Term.hole "_") (Term.hole "_")])]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       (Term.proj (Term.app `norm_sub_le [(Term.hole "_") (Term.hole "_")]) "." `trans)
       [(Term.app `add_le_add [(Term.hole "_") (Term.hole "_")])])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `add_le_add [(Term.hole "_") (Term.hole "_")])
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
      `add_le_add
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.app `add_le_add [(Term.hole "_") (Term.hole "_")])
     ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (Term.proj (Term.app `norm_sub_le [(Term.hole "_") (Term.hole "_")]) "." `trans)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.app `norm_sub_le [(Term.hole "_") (Term.hole "_")])
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
      `norm_sub_le
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.app `norm_sub_le [(Term.hole "_") (Term.hole "_")])
     ")")
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
        [(Tactic.rwRule
          [(patternIgnore (token.«← » "←"))]
          (Term.app
           `integral_sub
           [(Term.app `Hi [(Term.hole "_") `Hu]) (Term.app `Hi [(Term.hole "_") `Hl])]))]
        "]")
       [])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       `integral_sub
       [(Term.app `Hi [(Term.hole "_") `Hu]) (Term.app `Hi [(Term.hole "_") `Hl])])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `Hi [(Term.hole "_") `Hl])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `Hl
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `Hi
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.app `Hi [(Term.hole "_") `Hl])
     ")")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.app `Hi [(Term.hole "_") `Hu])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `Hu
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `Hi
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023,
     term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.app `Hi [(Term.hole "_") `Hu])
     ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `integral_sub
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.dsimp "dsimp" [] [] [] [] [])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.simp
       "simp"
       []
       []
       ["only"]
       ["["
        [(Tactic.simpLemma [] [] `dist_eq_norm)
         ","
         (Tactic.simpLemma [] [] `F)
         ","
         (Tactic.simpLemma [] [] `fI)]
        "]"]
       [])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `fI
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `F
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `dist_eq_norm
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.tacticHave_
       "have"
       (Term.haveDecl
        (Term.haveIdDecl
         [`Hmaps []]
         [(Term.typeSpec
           ":"
           (Std.ExtendedBinder.«term∀__,_»
            "∀"
            (Lean.binderIdent `z)
            («binderTerm∈_» "∈" (Term.app `Icc [(Term.app `J.lower [`i]) (Term.app `J.upper [`i])]))
            ","
            (Term.app
             `maps_to
             [(Term.app `i.insert_nth [`z])
              (Term.proj (Term.app `J.face [`i]) "." `IccCat)
              («term_∩_» (Term.app `closed_ball [`x `δ]) "∩" `I.Icc)])))]
         ":="
         (Term.fun
          "fun"
          (Term.basicFun
           [`z `hz]
           []
           "=>"
           (Term.app
            (Term.proj (Term.app `J.maps_to_insert_nth_face_Icc [`hz]) "." `mono)
            [`subset.rfl `hJδ']))))))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.fun
       "fun"
       (Term.basicFun
        [`z `hz]
        []
        "=>"
        (Term.app
         (Term.proj (Term.app `J.maps_to_insert_nth_face_Icc [`hz]) "." `mono)
         [`subset.rfl `hJδ'])))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       (Term.proj (Term.app `J.maps_to_insert_nth_face_Icc [`hz]) "." `mono)
       [`subset.rfl `hJδ'])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `hJδ'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `subset.rfl
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (Term.proj (Term.app `J.maps_to_insert_nth_face_Icc [`hz]) "." `mono)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.app `J.maps_to_insert_nth_face_Icc [`hz])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `hz
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `J.maps_to_insert_nth_face_Icc
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.app `J.maps_to_insert_nth_face_Icc [`hz])
     ")")
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.strictImplicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.implicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.instBinder'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `hz
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.strictImplicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.implicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.instBinder'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `z
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Std.ExtendedBinder.«term∀__,_»
       "∀"
       (Lean.binderIdent `z)
       («binderTerm∈_» "∈" (Term.app `Icc [(Term.app `J.lower [`i]) (Term.app `J.upper [`i])]))
       ","
       (Term.app
        `maps_to
        [(Term.app `i.insert_nth [`z])
         (Term.proj (Term.app `J.face [`i]) "." `IccCat)
         («term_∩_» (Term.app `closed_ball [`x `δ]) "∩" `I.Icc)]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       `maps_to
       [(Term.app `i.insert_nth [`z])
        (Term.proj (Term.app `J.face [`i]) "." `IccCat)
        («term_∩_» (Term.app `closed_ball [`x `δ]) "∩" `I.Icc)])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_∩_»', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_∩_»', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_∩_» (Term.app `closed_ball [`x `δ]) "∩" `I.Icc)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `I.Icc
[PrettyPrinter.parenthesize] ...precedences are 71 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 70, term))
      (Term.app `closed_ball [`x `δ])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `δ
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `x
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `closed_ball
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 70 >? 1022, (some 1023, term) <=? (some 70, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 70, (some 71, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     («term_∩_» (Term.app `closed_ball [`x `δ]) "∩" `I.Icc)
     ")")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.proj', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.proj', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.proj (Term.app `J.face [`i]) "." `IccCat)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.app `J.face [`i])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `i
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `J.face
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren "(" (Term.app `J.face [`i]) ")")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.app `i.insert_nth [`z])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `z
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `i.insert_nth
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023,
     term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren "(" (Term.app `i.insert_nth [`z]) ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `maps_to
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `Icc [(Term.app `J.lower [`i]) (Term.app `J.upper [`i])])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `J.upper [`i])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `i
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `J.upper
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren "(" (Term.app `J.upper [`i]) ")")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.app `J.lower [`i])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `i
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `J.lower
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023,
     term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren "(" (Term.app `J.lower [`i]) ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `Icc
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.tacticHave_
       "have"
       (Term.haveDecl
        (Term.haveIdDecl
         [`hJδ' []]
         [(Term.typeSpec
           ":"
           («term_⊆_» `J.Icc "⊆" («term_∩_» (Term.app `closed_ball [`x `δ]) "∩" `I.Icc)))]
         ":="
         (Term.app
          `subset_inter
          [`hJδ (Term.app (Term.proj `box.le_iff_Icc "." (fieldIdx "1")) [`hJI])]))))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       `subset_inter
       [`hJδ (Term.app (Term.proj `box.le_iff_Icc "." (fieldIdx "1")) [`hJI])])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app (Term.proj `box.le_iff_Icc "." (fieldIdx "1")) [`hJI])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `hJI
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (Term.proj `box.le_iff_Icc "." (fieldIdx "1"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `box.le_iff_Icc
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.app (Term.proj `box.le_iff_Icc "." (fieldIdx "1")) [`hJI])
     ")")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `hJδ
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `subset_inter
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_⊆_» `J.Icc "⊆" («term_∩_» (Term.app `closed_ball [`x `δ]) "∩" `I.Icc))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_∩_» (Term.app `closed_ball [`x `δ]) "∩" `I.Icc)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `I.Icc
[PrettyPrinter.parenthesize] ...precedences are 71 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 70, term))
      (Term.app `closed_ball [`x `δ])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `δ
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `x
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `closed_ball
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 70 >? 1022, (some 1023, term) <=? (some 70, term)
[PrettyPrinter.parenthesize] ...precedences are 51 >? 70, (some 71, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 50, term))
      `J.Icc
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1024, (none, [anonymous]) <=? (some 50, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 50, (some 51, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.tacticHave_
       "have"
       (Term.haveDecl
        (Term.haveIdDecl
         [`Hi []]
         [(Term.typeSpec
           ":"
           (Std.ExtendedBinder.«term∀__,_»
            "∀"
            (Lean.binderIdent `x)
            («binderTerm∈_» "∈" (Term.app `Icc [(Term.app `J.lower [`i]) (Term.app `J.upper [`i])]))
            ","
            (Term.app
             (Term.explicitUniv `Integrable ".{" [(num "0") "," `u "," `u] "}")
             [(Term.app `J.face [`i])
              `GP
              (Term.fun
               "fun"
               (Term.basicFun [`y] [] "=>" (Term.app `f [(Term.app `i.insert_nth [`x `y])])))
              `box_additive_map.volume])))]
         ":="
         (Term.fun
          "fun"
          (Term.basicFun
           [`x `hx]
           []
           "=>"
           (Term.app
            `integrable_of_continuous_on
            [(Term.hole "_")
             (Term.app
              `box.continuous_on_face_Icc
              [(«term_<|_»
                `Hc.mono
                "<|"
                (Term.app (Term.proj `box.le_iff_Icc "." (fieldIdx "1")) [`hJI]))
               `hx])
             `volume]))))))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.fun
       "fun"
       (Term.basicFun
        [`x `hx]
        []
        "=>"
        (Term.app
         `integrable_of_continuous_on
         [(Term.hole "_")
          (Term.app
           `box.continuous_on_face_Icc
           [(«term_<|_»
             `Hc.mono
             "<|"
             (Term.app (Term.proj `box.le_iff_Icc "." (fieldIdx "1")) [`hJI]))
            `hx])
          `volume])))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       `integrable_of_continuous_on
       [(Term.hole "_")
        (Term.app
         `box.continuous_on_face_Icc
         [(«term_<|_»
           `Hc.mono
           "<|"
           (Term.app (Term.proj `box.le_iff_Icc "." (fieldIdx "1")) [`hJI]))
          `hx])
        `volume])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `volume
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.app
       `box.continuous_on_face_Icc
       [(«term_<|_» `Hc.mono "<|" (Term.app (Term.proj `box.le_iff_Icc "." (fieldIdx "1")) [`hJI]))
        `hx])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `hx
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_<|_»', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_<|_»', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      («term_<|_» `Hc.mono "<|" (Term.app (Term.proj `box.le_iff_Icc "." (fieldIdx "1")) [`hJI]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app (Term.proj `box.le_iff_Icc "." (fieldIdx "1")) [`hJI])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `hJI
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (Term.proj `box.le_iff_Icc "." (fieldIdx "1"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `box.le_iff_Icc
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 10 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 10, term))
      `Hc.mono
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 10, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 10, (some 10, term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     («term_<|_» `Hc.mono "<|" (Term.app (Term.proj `box.le_iff_Icc "." (fieldIdx "1")) [`hJI]))
     ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `box.continuous_on_face_Icc
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023,
     term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.app
      `box.continuous_on_face_Icc
      [(Term.paren
        "("
        («term_<|_» `Hc.mono "<|" (Term.app (Term.proj `box.le_iff_Icc "." (fieldIdx "1")) [`hJI]))
        ")")
       `hx])
     ")")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `integrable_of_continuous_on
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.strictImplicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.implicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.instBinder'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `hx
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.strictImplicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.implicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.instBinder'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `x
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Std.ExtendedBinder.«term∀__,_»
       "∀"
       (Lean.binderIdent `x)
       («binderTerm∈_» "∈" (Term.app `Icc [(Term.app `J.lower [`i]) (Term.app `J.upper [`i])]))
       ","
       (Term.app
        (Term.explicitUniv `Integrable ".{" [(num "0") "," `u "," `u] "}")
        [(Term.app `J.face [`i])
         `GP
         (Term.fun
          "fun"
          (Term.basicFun [`y] [] "=>" (Term.app `f [(Term.app `i.insert_nth [`x `y])])))
         `box_additive_map.volume]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       (Term.explicitUniv `Integrable ".{" [(num "0") "," `u "," `u] "}")
       [(Term.app `J.face [`i])
        `GP
        (Term.fun
         "fun"
         (Term.basicFun [`y] [] "=>" (Term.app `f [(Term.app `i.insert_nth [`x `y])])))
        `box_additive_map.volume])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `box_additive_map.volume
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.fun "fun" (Term.basicFun [`y] [] "=>" (Term.app `f [(Term.app `i.insert_nth [`x `y])])))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `f [(Term.app `i.insert_nth [`x `y])])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `i.insert_nth [`x `y])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `y
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `x
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `i.insert_nth
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren "(" (Term.app `i.insert_nth [`x `y]) ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `f
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.strictImplicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.implicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.instBinder'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `y
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (some 0, term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.fun
      "fun"
      (Term.basicFun
       [`y]
       []
       "=>"
       (Term.app `f [(Term.paren "(" (Term.app `i.insert_nth [`x `y]) ")")])))
     ")")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `GP
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.app `J.face [`i])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `i
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `J.face
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023,
     term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren "(" (Term.app `J.face [`i]) ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (Term.explicitUniv `Integrable ".{" [(num "0") "," `u "," `u] "}")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `u
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `u
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (num "0")
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `Integrable
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `Icc [(Term.app `J.lower [`i]) (Term.app `J.upper [`i])])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `J.upper [`i])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `i
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `J.upper
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren "(" (Term.app `J.upper [`i]) ")")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.app `J.lower [`i])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `i
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `J.lower
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023,
     term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren "(" (Term.app `J.lower [`i]) ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `Icc
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.tacticHave_
       "have"
       (Term.haveDecl
        (Term.haveIdDecl
         [`Hu []]
         [(Term.typeSpec
           ":"
           («term_∈_»
            (Term.app `J.upper [`i])
            "∈"
            (Term.app `Icc [(Term.app `J.lower [`i]) (Term.app `J.upper [`i])])))]
         ":="
         (Term.app
          (Term.proj `Set.right_mem_Icc "." (fieldIdx "2"))
          [(Term.app `J.lower_le_upper [`i])]))))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       (Term.proj `Set.right_mem_Icc "." (fieldIdx "2"))
       [(Term.app `J.lower_le_upper [`i])])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `J.lower_le_upper [`i])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `i
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `J.lower_le_upper
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren "(" (Term.app `J.lower_le_upper [`i]) ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (Term.proj `Set.right_mem_Icc "." (fieldIdx "2"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `Set.right_mem_Icc
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_∈_»
       (Term.app `J.upper [`i])
       "∈"
       (Term.app `Icc [(Term.app `J.lower [`i]) (Term.app `J.upper [`i])]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `Icc [(Term.app `J.lower [`i]) (Term.app `J.upper [`i])])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `J.upper [`i])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `i
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `J.upper
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren "(" (Term.app `J.upper [`i]) ")")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.app `J.lower [`i])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `i
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `J.lower
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023,
     term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren "(" (Term.app `J.lower [`i]) ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `Icc
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 50, term))
      (Term.app `J.upper [`i])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `i
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `J.upper
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1022, (some 1023, term) <=? (some 50, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 50, (some 51, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.tacticHave_
       "have"
       (Term.haveDecl
        (Term.haveIdDecl
         [`Hl []]
         [(Term.typeSpec
           ":"
           («term_∈_»
            (Term.app `J.lower [`i])
            "∈"
            (Term.app `Icc [(Term.app `J.lower [`i]) (Term.app `J.upper [`i])])))]
         ":="
         (Term.app
          (Term.proj `Set.left_mem_Icc "." (fieldIdx "2"))
          [(Term.app `J.lower_le_upper [`i])]))))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       (Term.proj `Set.left_mem_Icc "." (fieldIdx "2"))
       [(Term.app `J.lower_le_upper [`i])])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `J.lower_le_upper [`i])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `i
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `J.lower_le_upper
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren "(" (Term.app `J.lower_le_upper [`i]) ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (Term.proj `Set.left_mem_Icc "." (fieldIdx "2"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `Set.left_mem_Icc
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_∈_»
       (Term.app `J.lower [`i])
       "∈"
       (Term.app `Icc [(Term.app `J.lower [`i]) (Term.app `J.upper [`i])]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `Icc [(Term.app `J.lower [`i]) (Term.app `J.upper [`i])])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `J.upper [`i])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `i
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `J.upper
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren "(" (Term.app `J.upper [`i]) ")")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.app `J.lower [`i])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `i
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `J.lower
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023,
     term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren "(" (Term.app `J.lower [`i]) ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `Icc
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 50, term))
      (Term.app `J.lower [`i])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `i
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `J.lower
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1022, (some 1023, term) <=? (some 50, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 50, (some 51, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.refine'
       "refine'"
       (Term.anonymousCtor
        "⟨"
        [`δ
         ","
         `hδ0
         ","
         (Term.fun
          "fun"
          (Term.basicFun
           [`J `hJI `hJδ `hxJ `hJc]
           []
           "=>"
           (Term.subst (Term.app `add_halves [`ε]) "▸" [(Term.hole "_")])))]
        "⟩"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.anonymousCtor
       "⟨"
       [`δ
        ","
        `hδ0
        ","
        (Term.fun
         "fun"
         (Term.basicFun
          [`J `hJI `hJδ `hxJ `hJc]
          []
          "=>"
          (Term.subst (Term.app `add_halves [`ε]) "▸" [(Term.hole "_")])))]
       "⟩")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.fun
       "fun"
       (Term.basicFun
        [`J `hJI `hJδ `hxJ `hJc]
        []
        "=>"
        (Term.subst (Term.app `add_halves [`ε]) "▸" [(Term.hole "_")])))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.subst (Term.app `add_halves [`ε]) "▸" [(Term.hole "_")])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 75 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 75, term))
      (Term.app `add_halves [`ε])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `ε
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `add_halves
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (some 75, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 75, (some 75, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.strictImplicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.implicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.instBinder'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `hJc
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.strictImplicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.implicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.instBinder'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `hxJ
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.strictImplicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.implicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.instBinder'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `hJδ
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.strictImplicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.implicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.instBinder'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `hJI
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.strictImplicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.implicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.instBinder'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `J
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `hδ0
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `δ
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Std.Tactic.rcases
       "rcases"
       [(Tactic.casesTarget [] `this.exists)]
       ["with"
        (Std.Tactic.RCases.rcasesPatLo
         (Std.Tactic.RCases.rcasesPatMed
          [(Std.Tactic.RCases.rcasesPat.tuple
            "⟨"
            [(Std.Tactic.RCases.rcasesPatLo
              (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `δ)])
              [])
             ","
             (Std.Tactic.RCases.rcasesPatLo
              (Std.Tactic.RCases.rcasesPatMed
               [(Std.Tactic.RCases.rcasesPat.tuple
                 "⟨"
                 [(Std.Tactic.RCases.rcasesPatLo
                   (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `hδ0)])
                   [])
                  ","
                  (Std.Tactic.RCases.rcasesPatLo
                   (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `hδ12)])
                   [])]
                 "⟩")])
              [])
             ","
             (Std.Tactic.RCases.rcasesPatLo
              (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `hdfδ)])
              [])
             ","
             (Std.Tactic.RCases.rcasesPatLo
              (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `hδ)])
              [])]
            "⟩")])
         [])])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `this.exists
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
           (Filter.Order.Filter.Basic.«term∀ᶠ_in_,_»
            "∀ᶠ"
            (Std.ExtendedBinder.extBinders (Std.ExtendedBinder.extBinder (Lean.binderIdent `δ) []))
            " in "
            (TopologicalSpace.Topology.Basic.nhds_within.gt
             "𝓝[>] "
             (Term.typeAscription "(" (num "0") ":" [(Data.Real.Basic.termℝ "ℝ")] ")"))
            ", "
            («term_∧_»
             («term_∈_»
              `δ
              "∈"
              (Term.app
               `Ioc
               [(Term.typeAscription "(" (num "0") ":" [(Data.Real.Basic.termℝ "ℝ")] ")")
                («term_/_» (num "1") "/" (num "2"))]))
             "∧"
             («term_∧_»
              (Term.forall
               "∀"
               [(Term.explicitBinder "(" [`y₁] [] [] ")")
                (Term.explicitBinder
                 "("
                 [(Term.hole "_")]
                 [":" («term_∈_» `y₁ "∈" («term_∩_» (Term.app `closed_ball [`x `δ]) "∩" `I.Icc))]
                 []
                 ")")
                (Term.explicitBinder "(" [`y₂] [] [] ")")
                (Term.explicitBinder
                 "("
                 [(Term.hole "_")]
                 [":" («term_∈_» `y₂ "∈" («term_∩_» (Term.app `closed_ball [`x `δ]) "∩" `I.Icc))]
                 []
                 ")")]
               []
               ","
               («term_≤_»
                (Analysis.Normed.Group.Basic.«term‖_‖»
                 "‖"
                 («term_-_» (Term.app `f [`y₁]) "-" (Term.app `f [`y₂]))
                 "‖")
                "≤"
                («term_/_» `ε "/" (num "2"))))
              "∧"
              («term_≤_»
               («term_*_»
                («term_^_» («term_*_» (num "2") "*" `δ) "^" («term_+_» `n "+" (num "1")))
                "*"
                (Analysis.Normed.Group.Basic.«term‖_‖»
                 "‖"
                 (Term.app `f' [`x (Term.app `Pi.single [`i (num "1")])])
                 "‖"))
               "≤"
               («term_/_» `ε "/" (num "2")))))))]
         ":="
         (Term.byTactic
          "by"
          (Tactic.tacticSeq
           (Tactic.tacticSeq1Indented
            [(Tactic.refine'
              "refine'"
              (Term.app
               `eventually.and
               [(Term.hole "_") (Term.app `eventually.and [(Term.hole "_") (Term.hole "_")])]))
             []
             (tactic__
              (cdotTk (patternIgnore (token.«· » "·")))
              [(Tactic.exact
                "exact"
                (Term.app
                 `Ioc_mem_nhds_within_Ioi
                 [(Term.anonymousCtor "⟨" [`le_rfl "," `one_half_pos] "⟩")]))])
             []
             (tactic__
              (cdotTk (patternIgnore (token.«· » "·")))
              [(Std.Tactic.rcases
                "rcases"
                [(Tactic.casesTarget
                  []
                  (Term.app
                   (Term.proj
                    (Term.app
                     (Term.proj
                      (Term.app `nhds_within_has_basis [`nhds_basis_closed_ball (Term.hole "_")])
                      "."
                      `tendsto_iff)
                     [`nhds_basis_closed_ball])
                    "."
                    (fieldIdx "1"))
                   [(Term.app `Hs [`x (Term.proj `hx "." (fieldIdx "2"))])
                    (Term.hole "_")
                    («term_<|_» `half_pos "<|" (Term.app `half_pos [`ε0]))]))]
                ["with"
                 (Std.Tactic.RCases.rcasesPatLo
                  (Std.Tactic.RCases.rcasesPatMed
                   [(Std.Tactic.RCases.rcasesPat.tuple
                     "⟨"
                     [(Std.Tactic.RCases.rcasesPatLo
                       (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `δ₁)])
                       [])
                      ","
                      (Std.Tactic.RCases.rcasesPatLo
                       (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `δ₁0)])
                       [])
                      ","
                      (Std.Tactic.RCases.rcasesPatLo
                       (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `hδ₁)])
                       [])]
                     "⟩")])
                  [])])
               []
               (Tactic.filterUpwards
                "filter_upwards"
                [(Tactic.termList
                  "["
                  [(Term.app
                    `Ioc_mem_nhds_within_Ioi
                    [(Term.anonymousCtor "⟨" [`le_rfl "," `δ₁0] "⟩")])]
                  "]")]
                ["with" [`δ `hδ `y₁ `hy₁ `y₂ `hy₂]]
                [])
               []
               (Tactic.tacticHave_
                "have"
                (Term.haveDecl
                 (Term.haveIdDecl
                  []
                  [(Term.typeSpec
                    ":"
                    («term_⊆_»
                     («term_∩_» (Term.app `closed_ball [`x `δ]) "∩" `I.Icc)
                     "⊆"
                     («term_∩_» (Term.app `closed_ball [`x `δ₁]) "∩" `I.Icc)))]
                  ":="
                  (Term.app
                   `inter_subset_inter_left
                   [(Term.hole "_")
                    (Term.app
                     `closed_ball_subset_closed_ball
                     [(Term.proj `hδ "." (fieldIdx "2"))])]))))
               []
               (Tactic.rwSeq
                "rw"
                []
                (Tactic.rwRuleSeq
                 "["
                 [(Tactic.rwRule [(patternIgnore (token.«← » "←"))] `dist_eq_norm)]
                 "]")
                [])
               []
               (calcTactic
                "calc"
                (calcStep
                 («term_≤_»
                  (Term.app `dist [(Term.app `f [`y₁]) (Term.app `f [`y₂])])
                  "≤"
                  («term_+_»
                   (Term.app `dist [(Term.app `f [`y₁]) (Term.app `f [`x])])
                   "+"
                   (Term.app `dist [(Term.app `f [`y₂]) (Term.app `f [`x])])))
                 ":="
                 (Term.app `dist_triangle_right [(Term.hole "_") (Term.hole "_") (Term.hole "_")]))
                [(calcStep
                  («term_≤_»
                   (Term.hole "_")
                   "≤"
                   («term_+_»
                    («term_/_» («term_/_» `ε "/" (num "2")) "/" (num "2"))
                    "+"
                    («term_/_» («term_/_» `ε "/" (num "2")) "/" (num "2"))))
                  ":="
                  (Term.app
                   `add_le_add
                   [(«term_<|_» (Term.app `hδ₁ [(Term.hole "_")]) "<|" (Term.app `this [`hy₁]))
                    («term_<|_» (Term.app `hδ₁ [(Term.hole "_")]) "<|" (Term.app `this [`hy₂]))]))
                 (calcStep
                  («term_=_» (Term.hole "_") "=" («term_/_» `ε "/" (num "2")))
                  ":="
                  (Term.app `add_halves [(Term.hole "_")]))])])
             []
             (tactic__
              (cdotTk (patternIgnore (token.«· » "·")))
              [(Tactic.tacticHave_
                "have"
                (Term.haveDecl
                 (Term.haveIdDecl
                  []
                  [(Term.typeSpec
                    ":"
                    (Term.app
                     `ContinuousWithinAt
                     [(Term.fun
                       "fun"
                       (Term.basicFun
                        [`δ]
                        []
                        "=>"
                        («term_*_»
                         («term_^_» («term_*_» (num "2") "*" `δ) "^" («term_+_» `n "+" (num "1")))
                         "*"
                         (Analysis.Normed.Group.Basic.«term‖_‖»
                          "‖"
                          (Term.app `f' [`x (Term.app `Pi.single [`i (num "1")])])
                          "‖"))))
                      (Term.app
                       `Ioi
                       [(Term.typeAscription "(" (num "0") ":" [(Data.Real.Basic.termℝ "ℝ")] ")")])
                      (num "0")]))]
                  ":="
                  (Term.app
                   (Term.proj
                    (Term.app
                     (Term.proj
                      (Term.app `continuous_within_at_id.const_mul [(Term.hole "_")])
                      "."
                      `pow)
                     [(Term.hole "_")])
                    "."
                    `mul_const)
                   [(Term.hole "_")]))))
               []
               (Tactic.refine'
                "refine'"
                (Term.app `this.eventually [(Term.app `ge_mem_nhds [(Term.hole "_")])]))
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
                 ["using" (Term.app `half_pos [`ε0])]))])]))))))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.byTactic
       "by"
       (Tactic.tacticSeq
        (Tactic.tacticSeq1Indented
         [(Tactic.refine'
           "refine'"
           (Term.app
            `eventually.and
            [(Term.hole "_") (Term.app `eventually.and [(Term.hole "_") (Term.hole "_")])]))
          []
          (tactic__
           (cdotTk (patternIgnore (token.«· » "·")))
           [(Tactic.exact
             "exact"
             (Term.app
              `Ioc_mem_nhds_within_Ioi
              [(Term.anonymousCtor "⟨" [`le_rfl "," `one_half_pos] "⟩")]))])
          []
          (tactic__
           (cdotTk (patternIgnore (token.«· » "·")))
           [(Std.Tactic.rcases
             "rcases"
             [(Tactic.casesTarget
               []
               (Term.app
                (Term.proj
                 (Term.app
                  (Term.proj
                   (Term.app `nhds_within_has_basis [`nhds_basis_closed_ball (Term.hole "_")])
                   "."
                   `tendsto_iff)
                  [`nhds_basis_closed_ball])
                 "."
                 (fieldIdx "1"))
                [(Term.app `Hs [`x (Term.proj `hx "." (fieldIdx "2"))])
                 (Term.hole "_")
                 («term_<|_» `half_pos "<|" (Term.app `half_pos [`ε0]))]))]
             ["with"
              (Std.Tactic.RCases.rcasesPatLo
               (Std.Tactic.RCases.rcasesPatMed
                [(Std.Tactic.RCases.rcasesPat.tuple
                  "⟨"
                  [(Std.Tactic.RCases.rcasesPatLo
                    (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `δ₁)])
                    [])
                   ","
                   (Std.Tactic.RCases.rcasesPatLo
                    (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `δ₁0)])
                    [])
                   ","
                   (Std.Tactic.RCases.rcasesPatLo
                    (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `hδ₁)])
                    [])]
                  "⟩")])
               [])])
            []
            (Tactic.filterUpwards
             "filter_upwards"
             [(Tactic.termList
               "["
               [(Term.app
                 `Ioc_mem_nhds_within_Ioi
                 [(Term.anonymousCtor "⟨" [`le_rfl "," `δ₁0] "⟩")])]
               "]")]
             ["with" [`δ `hδ `y₁ `hy₁ `y₂ `hy₂]]
             [])
            []
            (Tactic.tacticHave_
             "have"
             (Term.haveDecl
              (Term.haveIdDecl
               []
               [(Term.typeSpec
                 ":"
                 («term_⊆_»
                  («term_∩_» (Term.app `closed_ball [`x `δ]) "∩" `I.Icc)
                  "⊆"
                  («term_∩_» (Term.app `closed_ball [`x `δ₁]) "∩" `I.Icc)))]
               ":="
               (Term.app
                `inter_subset_inter_left
                [(Term.hole "_")
                 (Term.app
                  `closed_ball_subset_closed_ball
                  [(Term.proj `hδ "." (fieldIdx "2"))])]))))
            []
            (Tactic.rwSeq
             "rw"
             []
             (Tactic.rwRuleSeq
              "["
              [(Tactic.rwRule [(patternIgnore (token.«← » "←"))] `dist_eq_norm)]
              "]")
             [])
            []
            (calcTactic
             "calc"
             (calcStep
              («term_≤_»
               (Term.app `dist [(Term.app `f [`y₁]) (Term.app `f [`y₂])])
               "≤"
               («term_+_»
                (Term.app `dist [(Term.app `f [`y₁]) (Term.app `f [`x])])
                "+"
                (Term.app `dist [(Term.app `f [`y₂]) (Term.app `f [`x])])))
              ":="
              (Term.app `dist_triangle_right [(Term.hole "_") (Term.hole "_") (Term.hole "_")]))
             [(calcStep
               («term_≤_»
                (Term.hole "_")
                "≤"
                («term_+_»
                 («term_/_» («term_/_» `ε "/" (num "2")) "/" (num "2"))
                 "+"
                 («term_/_» («term_/_» `ε "/" (num "2")) "/" (num "2"))))
               ":="
               (Term.app
                `add_le_add
                [(«term_<|_» (Term.app `hδ₁ [(Term.hole "_")]) "<|" (Term.app `this [`hy₁]))
                 («term_<|_» (Term.app `hδ₁ [(Term.hole "_")]) "<|" (Term.app `this [`hy₂]))]))
              (calcStep
               («term_=_» (Term.hole "_") "=" («term_/_» `ε "/" (num "2")))
               ":="
               (Term.app `add_halves [(Term.hole "_")]))])])
          []
          (tactic__
           (cdotTk (patternIgnore (token.«· » "·")))
           [(Tactic.tacticHave_
             "have"
             (Term.haveDecl
              (Term.haveIdDecl
               []
               [(Term.typeSpec
                 ":"
                 (Term.app
                  `ContinuousWithinAt
                  [(Term.fun
                    "fun"
                    (Term.basicFun
                     [`δ]
                     []
                     "=>"
                     («term_*_»
                      («term_^_» («term_*_» (num "2") "*" `δ) "^" («term_+_» `n "+" (num "1")))
                      "*"
                      (Analysis.Normed.Group.Basic.«term‖_‖»
                       "‖"
                       (Term.app `f' [`x (Term.app `Pi.single [`i (num "1")])])
                       "‖"))))
                   (Term.app
                    `Ioi
                    [(Term.typeAscription "(" (num "0") ":" [(Data.Real.Basic.termℝ "ℝ")] ")")])
                   (num "0")]))]
               ":="
               (Term.app
                (Term.proj
                 (Term.app
                  (Term.proj
                   (Term.app `continuous_within_at_id.const_mul [(Term.hole "_")])
                   "."
                   `pow)
                  [(Term.hole "_")])
                 "."
                 `mul_const)
                [(Term.hole "_")]))))
            []
            (Tactic.refine'
             "refine'"
             (Term.app `this.eventually [(Term.app `ge_mem_nhds [(Term.hole "_")])]))
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
              ["using" (Term.app `half_pos [`ε0])]))])])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (tactic__
       (cdotTk (patternIgnore (token.«· » "·")))
       [(Tactic.tacticHave_
         "have"
         (Term.haveDecl
          (Term.haveIdDecl
           []
           [(Term.typeSpec
             ":"
             (Term.app
              `ContinuousWithinAt
              [(Term.fun
                "fun"
                (Term.basicFun
                 [`δ]
                 []
                 "=>"
                 («term_*_»
                  («term_^_» («term_*_» (num "2") "*" `δ) "^" («term_+_» `n "+" (num "1")))
                  "*"
                  (Analysis.Normed.Group.Basic.«term‖_‖»
                   "‖"
                   (Term.app `f' [`x (Term.app `Pi.single [`i (num "1")])])
                   "‖"))))
               (Term.app
                `Ioi
                [(Term.typeAscription "(" (num "0") ":" [(Data.Real.Basic.termℝ "ℝ")] ")")])
               (num "0")]))]
           ":="
           (Term.app
            (Term.proj
             (Term.app
              (Term.proj (Term.app `continuous_within_at_id.const_mul [(Term.hole "_")]) "." `pow)
              [(Term.hole "_")])
             "."
             `mul_const)
            [(Term.hole "_")]))))
        []
        (Tactic.refine'
         "refine'"
         (Term.app `this.eventually [(Term.app `ge_mem_nhds [(Term.hole "_")])]))
        []
        (Std.Tactic.Simpa.simpa
         "simpa"
         []
         []
         (Std.Tactic.Simpa.simpaArgsRest [] [] [] [] ["using" (Term.app `half_pos [`ε0])]))])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Std.Tactic.Simpa.simpa
       "simpa"
       []
       []
       (Std.Tactic.Simpa.simpaArgsRest [] [] [] [] ["using" (Term.app `half_pos [`ε0])]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `half_pos [`ε0])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `ε0
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `half_pos
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.refine'
       "refine'"
       (Term.app `this.eventually [(Term.app `ge_mem_nhds [(Term.hole "_")])]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `this.eventually [(Term.app `ge_mem_nhds [(Term.hole "_")])])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `ge_mem_nhds [(Term.hole "_")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `ge_mem_nhds
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.app `ge_mem_nhds [(Term.hole "_")])
     ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `this.eventually
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
           (Term.app
            `ContinuousWithinAt
            [(Term.fun
              "fun"
              (Term.basicFun
               [`δ]
               []
               "=>"
               («term_*_»
                («term_^_» («term_*_» (num "2") "*" `δ) "^" («term_+_» `n "+" (num "1")))
                "*"
                (Analysis.Normed.Group.Basic.«term‖_‖»
                 "‖"
                 (Term.app `f' [`x (Term.app `Pi.single [`i (num "1")])])
                 "‖"))))
             (Term.app
              `Ioi
              [(Term.typeAscription "(" (num "0") ":" [(Data.Real.Basic.termℝ "ℝ")] ")")])
             (num "0")]))]
         ":="
         (Term.app
          (Term.proj
           (Term.app
            (Term.proj (Term.app `continuous_within_at_id.const_mul [(Term.hole "_")]) "." `pow)
            [(Term.hole "_")])
           "."
           `mul_const)
          [(Term.hole "_")]))))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       (Term.proj
        (Term.app
         (Term.proj (Term.app `continuous_within_at_id.const_mul [(Term.hole "_")]) "." `pow)
         [(Term.hole "_")])
        "."
        `mul_const)
       [(Term.hole "_")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (Term.proj
       (Term.app
        (Term.proj (Term.app `continuous_within_at_id.const_mul [(Term.hole "_")]) "." `pow)
        [(Term.hole "_")])
       "."
       `mul_const)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.app
       (Term.proj (Term.app `continuous_within_at_id.const_mul [(Term.hole "_")]) "." `pow)
       [(Term.hole "_")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (Term.proj (Term.app `continuous_within_at_id.const_mul [(Term.hole "_")]) "." `pow)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.app `continuous_within_at_id.const_mul [(Term.hole "_")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `continuous_within_at_id.const_mul
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.app `continuous_within_at_id.const_mul [(Term.hole "_")])
     ")")
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.app
      (Term.proj
       (Term.paren "(" (Term.app `continuous_within_at_id.const_mul [(Term.hole "_")]) ")")
       "."
       `pow)
      [(Term.hole "_")])
     ")")
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       `ContinuousWithinAt
       [(Term.fun
         "fun"
         (Term.basicFun
          [`δ]
          []
          "=>"
          («term_*_»
           («term_^_» («term_*_» (num "2") "*" `δ) "^" («term_+_» `n "+" (num "1")))
           "*"
           (Analysis.Normed.Group.Basic.«term‖_‖»
            "‖"
            (Term.app `f' [`x (Term.app `Pi.single [`i (num "1")])])
            "‖"))))
        (Term.app `Ioi [(Term.typeAscription "(" (num "0") ":" [(Data.Real.Basic.termℝ "ℝ")] ")")])
        (num "0")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'num', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'num', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (num "0")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.app `Ioi [(Term.typeAscription "(" (num "0") ":" [(Data.Real.Basic.termℝ "ℝ")] ")")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.typeAscription', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.typeAscription', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.typeAscription "(" (num "0") ":" [(Data.Real.Basic.termℝ "ℝ")] ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Data.Real.Basic.termℝ "ℝ")
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (num "0")
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `Ioi
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023,
     term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.app `Ioi [(Term.typeAscription "(" (num "0") ":" [(Data.Real.Basic.termℝ "ℝ")] ")")])
     ")")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.fun
       "fun"
       (Term.basicFun
        [`δ]
        []
        "=>"
        («term_*_»
         («term_^_» («term_*_» (num "2") "*" `δ) "^" («term_+_» `n "+" (num "1")))
         "*"
         (Analysis.Normed.Group.Basic.«term‖_‖»
          "‖"
          (Term.app `f' [`x (Term.app `Pi.single [`i (num "1")])])
          "‖"))))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_*_»
       («term_^_» («term_*_» (num "2") "*" `δ) "^" («term_+_» `n "+" (num "1")))
       "*"
       (Analysis.Normed.Group.Basic.«term‖_‖»
        "‖"
        (Term.app `f' [`x (Term.app `Pi.single [`i (num "1")])])
        "‖"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Analysis.Normed.Group.Basic.«term‖_‖»
       "‖"
       (Term.app `f' [`x (Term.app `Pi.single [`i (num "1")])])
       "‖")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `f' [`x (Term.app `Pi.single [`i (num "1")])])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `Pi.single [`i (num "1")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'num', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'num', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (num "1")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `i
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `Pi.single
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.app `Pi.single [`i (num "1")])
     ")")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `x
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `f'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 71 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 70, term))
      («term_^_» («term_*_» (num "2") "*" `δ) "^" («term_+_» `n "+" (num "1")))
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
      («term_*_» (num "2") "*" `δ)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `δ
[PrettyPrinter.parenthesize] ...precedences are 71 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 70, term))
      (num "2")
[PrettyPrinter.parenthesize] ...precedences are 70 >? 1024, (none, [anonymous]) <=? (some 70, term)
[PrettyPrinter.parenthesize] ...precedences are 81 >? 70, (some 71, term) <=? (some 80, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren "(" («term_*_» (num "2") "*" `δ) ")")
[PrettyPrinter.parenthesize] ...precedences are 70 >? 80, (some 80, term) <=? (some 70, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 70, (some 71, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.strictImplicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.implicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.instBinder'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `δ
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (some 0, term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.fun
      "fun"
      (Term.basicFun
       [`δ]
       []
       "=>"
       («term_*_»
        («term_^_»
         (Term.paren "(" («term_*_» (num "2") "*" `δ) ")")
         "^"
         (Term.paren "(" («term_+_» `n "+" (num "1")) ")"))
        "*"
        (Analysis.Normed.Group.Basic.«term‖_‖»
         "‖"
         (Term.app `f' [`x (Term.paren "(" (Term.app `Pi.single [`i (num "1")]) ")")])
         "‖"))))
     ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `ContinuousWithinAt
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (tactic__
       (cdotTk (patternIgnore (token.«· » "·")))
       [(Std.Tactic.rcases
         "rcases"
         [(Tactic.casesTarget
           []
           (Term.app
            (Term.proj
             (Term.app
              (Term.proj
               (Term.app `nhds_within_has_basis [`nhds_basis_closed_ball (Term.hole "_")])
               "."
               `tendsto_iff)
              [`nhds_basis_closed_ball])
             "."
             (fieldIdx "1"))
            [(Term.app `Hs [`x (Term.proj `hx "." (fieldIdx "2"))])
             (Term.hole "_")
             («term_<|_» `half_pos "<|" (Term.app `half_pos [`ε0]))]))]
         ["with"
          (Std.Tactic.RCases.rcasesPatLo
           (Std.Tactic.RCases.rcasesPatMed
            [(Std.Tactic.RCases.rcasesPat.tuple
              "⟨"
              [(Std.Tactic.RCases.rcasesPatLo
                (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `δ₁)])
                [])
               ","
               (Std.Tactic.RCases.rcasesPatLo
                (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `δ₁0)])
                [])
               ","
               (Std.Tactic.RCases.rcasesPatLo
                (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `hδ₁)])
                [])]
              "⟩")])
           [])])
        []
        (Tactic.filterUpwards
         "filter_upwards"
         [(Tactic.termList
           "["
           [(Term.app `Ioc_mem_nhds_within_Ioi [(Term.anonymousCtor "⟨" [`le_rfl "," `δ₁0] "⟩")])]
           "]")]
         ["with" [`δ `hδ `y₁ `hy₁ `y₂ `hy₂]]
         [])
        []
        (Tactic.tacticHave_
         "have"
         (Term.haveDecl
          (Term.haveIdDecl
           []
           [(Term.typeSpec
             ":"
             («term_⊆_»
              («term_∩_» (Term.app `closed_ball [`x `δ]) "∩" `I.Icc)
              "⊆"
              («term_∩_» (Term.app `closed_ball [`x `δ₁]) "∩" `I.Icc)))]
           ":="
           (Term.app
            `inter_subset_inter_left
            [(Term.hole "_")
             (Term.app `closed_ball_subset_closed_ball [(Term.proj `hδ "." (fieldIdx "2"))])]))))
        []
        (Tactic.rwSeq
         "rw"
         []
         (Tactic.rwRuleSeq
          "["
          [(Tactic.rwRule [(patternIgnore (token.«← » "←"))] `dist_eq_norm)]
          "]")
         [])
        []
        (calcTactic
         "calc"
         (calcStep
          («term_≤_»
           (Term.app `dist [(Term.app `f [`y₁]) (Term.app `f [`y₂])])
           "≤"
           («term_+_»
            (Term.app `dist [(Term.app `f [`y₁]) (Term.app `f [`x])])
            "+"
            (Term.app `dist [(Term.app `f [`y₂]) (Term.app `f [`x])])))
          ":="
          (Term.app `dist_triangle_right [(Term.hole "_") (Term.hole "_") (Term.hole "_")]))
         [(calcStep
           («term_≤_»
            (Term.hole "_")
            "≤"
            («term_+_»
             («term_/_» («term_/_» `ε "/" (num "2")) "/" (num "2"))
             "+"
             («term_/_» («term_/_» `ε "/" (num "2")) "/" (num "2"))))
           ":="
           (Term.app
            `add_le_add
            [(«term_<|_» (Term.app `hδ₁ [(Term.hole "_")]) "<|" (Term.app `this [`hy₁]))
             («term_<|_» (Term.app `hδ₁ [(Term.hole "_")]) "<|" (Term.app `this [`hy₂]))]))
          (calcStep
           («term_=_» (Term.hole "_") "=" («term_/_» `ε "/" (num "2")))
           ":="
           (Term.app `add_halves [(Term.hole "_")]))])])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (calcTactic
       "calc"
       (calcStep
        («term_≤_»
         (Term.app `dist [(Term.app `f [`y₁]) (Term.app `f [`y₂])])
         "≤"
         («term_+_»
          (Term.app `dist [(Term.app `f [`y₁]) (Term.app `f [`x])])
          "+"
          (Term.app `dist [(Term.app `f [`y₂]) (Term.app `f [`x])])))
        ":="
        (Term.app `dist_triangle_right [(Term.hole "_") (Term.hole "_") (Term.hole "_")]))
       [(calcStep
         («term_≤_»
          (Term.hole "_")
          "≤"
          («term_+_»
           («term_/_» («term_/_» `ε "/" (num "2")) "/" (num "2"))
           "+"
           («term_/_» («term_/_» `ε "/" (num "2")) "/" (num "2"))))
         ":="
         (Term.app
          `add_le_add
          [(«term_<|_» (Term.app `hδ₁ [(Term.hole "_")]) "<|" (Term.app `this [`hy₁]))
           («term_<|_» (Term.app `hδ₁ [(Term.hole "_")]) "<|" (Term.app `this [`hy₂]))]))
        (calcStep
         («term_=_» (Term.hole "_") "=" («term_/_» `ε "/" (num "2")))
         ":="
         (Term.app `add_halves [(Term.hole "_")]))])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `add_halves [(Term.hole "_")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `add_halves
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_=_» (Term.hole "_") "=" («term_/_» `ε "/" (num "2")))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_/_» `ε "/" (num "2"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (num "2")
[PrettyPrinter.parenthesize] ...precedences are 71 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 70, term))
      `ε
[PrettyPrinter.parenthesize] ...precedences are 70 >? 1024, (none, [anonymous]) <=? (some 70, term)
[PrettyPrinter.parenthesize] ...precedences are 51 >? 70, (some 71, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 50, term))
      (Term.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1024, (none, [anonymous]) <=? (some 50, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 50, (some 51, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, term))
      (Term.app
       `add_le_add
       [(«term_<|_» (Term.app `hδ₁ [(Term.hole "_")]) "<|" (Term.app `this [`hy₁]))
        («term_<|_» (Term.app `hδ₁ [(Term.hole "_")]) "<|" (Term.app `this [`hy₂]))])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_<|_»', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_<|_»', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_<|_» (Term.app `hδ₁ [(Term.hole "_")]) "<|" (Term.app `this [`hy₂]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `this [`hy₂])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `hy₂
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `this
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 10 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 10, term))
      (Term.app `hδ₁ [(Term.hole "_")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `hδ₁
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (some 10, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 10, (some 10, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     («term_<|_» (Term.app `hδ₁ [(Term.hole "_")]) "<|" (Term.app `this [`hy₂]))
     ")")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_<|_»', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_<|_»', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      («term_<|_» (Term.app `hδ₁ [(Term.hole "_")]) "<|" (Term.app `this [`hy₁]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `this [`hy₁])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `hy₁
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `this
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 10 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 10, term))
      (Term.app `hδ₁ [(Term.hole "_")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `hδ₁
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (some 10, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 10, (some 10, term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     («term_<|_» (Term.app `hδ₁ [(Term.hole "_")]) "<|" (Term.app `this [`hy₁]))
     ")")
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
        («term_/_» («term_/_» `ε "/" (num "2")) "/" (num "2"))
        "+"
        («term_/_» («term_/_» `ε "/" (num "2")) "/" (num "2"))))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_+_»
       («term_/_» («term_/_» `ε "/" (num "2")) "/" (num "2"))
       "+"
       («term_/_» («term_/_» `ε "/" (num "2")) "/" (num "2")))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_/_» («term_/_» `ε "/" (num "2")) "/" (num "2"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (num "2")
[PrettyPrinter.parenthesize] ...precedences are 71 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 70, term))
      («term_/_» `ε "/" (num "2"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (num "2")
[PrettyPrinter.parenthesize] ...precedences are 71 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 70, term))
      `ε
[PrettyPrinter.parenthesize] ...precedences are 70 >? 1024, (none, [anonymous]) <=? (some 70, term)
[PrettyPrinter.parenthesize] ...precedences are 70 >? 70, (some 71, term) <=? (some 70, term)
[PrettyPrinter.parenthesize] ...precedences are 66 >? 70, (some 71, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 65, term))
      («term_/_» («term_/_» `ε "/" (num "2")) "/" (num "2"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (num "2")
[PrettyPrinter.parenthesize] ...precedences are 71 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 70, term))
      («term_/_» `ε "/" (num "2"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (num "2")
[PrettyPrinter.parenthesize] ...precedences are 71 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 70, term))
      `ε
[PrettyPrinter.parenthesize] ...precedences are 70 >? 1024, (none, [anonymous]) <=? (some 70, term)
[PrettyPrinter.parenthesize] ...precedences are 70 >? 70, (some 71, term) <=? (some 70, term)
[PrettyPrinter.parenthesize] ...precedences are 65 >? 70, (some 71, term) <=? (some 65, term)
[PrettyPrinter.parenthesize] ...precedences are 51 >? 65, (some 66, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 50, term))
      (Term.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1024, (none, [anonymous]) <=? (some 50, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 50, (some 51, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, term))
      (Term.app `dist_triangle_right [(Term.hole "_") (Term.hole "_") (Term.hole "_")])
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
      `dist_triangle_right
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_≤_»
       (Term.app `dist [(Term.app `f [`y₁]) (Term.app `f [`y₂])])
       "≤"
       («term_+_»
        (Term.app `dist [(Term.app `f [`y₁]) (Term.app `f [`x])])
        "+"
        (Term.app `dist [(Term.app `f [`y₂]) (Term.app `f [`x])])))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_+_»
       (Term.app `dist [(Term.app `f [`y₁]) (Term.app `f [`x])])
       "+"
       (Term.app `dist [(Term.app `f [`y₂]) (Term.app `f [`x])]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `dist [(Term.app `f [`y₂]) (Term.app `f [`x])])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
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
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren "(" (Term.app `f [`x]) ")")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.app `f [`y₂])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `y₂
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `f
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023,
     term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren "(" (Term.app `f [`y₂]) ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `dist
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 66 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 65, term))
      (Term.app `dist [(Term.app `f [`y₁]) (Term.app `f [`x])])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
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
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren "(" (Term.app `f [`x]) ")")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.app `f [`y₁])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `y₁
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `f
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023,
     term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren "(" (Term.app `f [`y₁]) ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `dist
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 65 >? 1022, (some 1023, term) <=? (some 65, term)
[PrettyPrinter.parenthesize] ...precedences are 51 >? 65, (some 66, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 50, term))
      (Term.app `dist [(Term.app `f [`y₁]) (Term.app `f [`y₂])])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `f [`y₂])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `y₂
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `f
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren "(" (Term.app `f [`y₂]) ")")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.app `f [`y₁])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `y₁
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `f
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023,
     term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren "(" (Term.app `f [`y₁]) ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `dist
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1022, (some 1023, term) <=? (some 50, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 50, (some 51, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.rwSeq
       "rw"
       []
       (Tactic.rwRuleSeq "[" [(Tactic.rwRule [(patternIgnore (token.«← » "←"))] `dist_eq_norm)] "]")
       [])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `dist_eq_norm
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
           («term_⊆_»
            («term_∩_» (Term.app `closed_ball [`x `δ]) "∩" `I.Icc)
            "⊆"
            («term_∩_» (Term.app `closed_ball [`x `δ₁]) "∩" `I.Icc)))]
         ":="
         (Term.app
          `inter_subset_inter_left
          [(Term.hole "_")
           (Term.app `closed_ball_subset_closed_ball [(Term.proj `hδ "." (fieldIdx "2"))])]))))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       `inter_subset_inter_left
       [(Term.hole "_")
        (Term.app `closed_ball_subset_closed_ball [(Term.proj `hδ "." (fieldIdx "2"))])])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `closed_ball_subset_closed_ball [(Term.proj `hδ "." (fieldIdx "2"))])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.proj', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.proj', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.proj `hδ "." (fieldIdx "2"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `hδ
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `closed_ball_subset_closed_ball
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.app `closed_ball_subset_closed_ball [(Term.proj `hδ "." (fieldIdx "2"))])
     ")")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `inter_subset_inter_left
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_⊆_»
       («term_∩_» (Term.app `closed_ball [`x `δ]) "∩" `I.Icc)
       "⊆"
       («term_∩_» (Term.app `closed_ball [`x `δ₁]) "∩" `I.Icc))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_∩_» (Term.app `closed_ball [`x `δ₁]) "∩" `I.Icc)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `I.Icc
[PrettyPrinter.parenthesize] ...precedences are 71 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 70, term))
      (Term.app `closed_ball [`x `δ₁])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `δ₁
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `x
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `closed_ball
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 70 >? 1022, (some 1023, term) <=? (some 70, term)
[PrettyPrinter.parenthesize] ...precedences are 51 >? 70, (some 71, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 50, term))
      («term_∩_» (Term.app `closed_ball [`x `δ]) "∩" `I.Icc)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `I.Icc
[PrettyPrinter.parenthesize] ...precedences are 71 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 70, term))
      (Term.app `closed_ball [`x `δ])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `δ
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `x
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `closed_ball
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 70 >? 1022, (some 1023, term) <=? (some 70, term)
[PrettyPrinter.parenthesize] ...precedences are 51 >? 70, (some 71, term) <=? (some 50, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 50, (some 51, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.filterUpwards
       "filter_upwards"
       [(Tactic.termList
         "["
         [(Term.app `Ioc_mem_nhds_within_Ioi [(Term.anonymousCtor "⟨" [`le_rfl "," `δ₁0] "⟩")])]
         "]")]
       ["with" [`δ `hδ `y₁ `hy₁ `y₂ `hy₂]]
       [])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `hy₂
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `y₂
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `hy₁
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `y₁
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `hδ
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `δ
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `Ioc_mem_nhds_within_Ioi [(Term.anonymousCtor "⟨" [`le_rfl "," `δ₁0] "⟩")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.anonymousCtor', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.anonymousCtor', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.anonymousCtor "⟨" [`le_rfl "," `δ₁0] "⟩")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `δ₁0
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `le_rfl
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `Ioc_mem_nhds_within_Ioi
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
          (Term.proj
           (Term.app
            (Term.proj
             (Term.app `nhds_within_has_basis [`nhds_basis_closed_ball (Term.hole "_")])
             "."
             `tendsto_iff)
            [`nhds_basis_closed_ball])
           "."
           (fieldIdx "1"))
          [(Term.app `Hs [`x (Term.proj `hx "." (fieldIdx "2"))])
           (Term.hole "_")
           («term_<|_» `half_pos "<|" (Term.app `half_pos [`ε0]))]))]
       ["with"
        (Std.Tactic.RCases.rcasesPatLo
         (Std.Tactic.RCases.rcasesPatMed
          [(Std.Tactic.RCases.rcasesPat.tuple
            "⟨"
            [(Std.Tactic.RCases.rcasesPatLo
              (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `δ₁)])
              [])
             ","
             (Std.Tactic.RCases.rcasesPatLo
              (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `δ₁0)])
              [])
             ","
             (Std.Tactic.RCases.rcasesPatLo
              (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `hδ₁)])
              [])]
            "⟩")])
         [])])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       (Term.proj
        (Term.app
         (Term.proj
          (Term.app `nhds_within_has_basis [`nhds_basis_closed_ball (Term.hole "_")])
          "."
          `tendsto_iff)
         [`nhds_basis_closed_ball])
        "."
        (fieldIdx "1"))
       [(Term.app `Hs [`x (Term.proj `hx "." (fieldIdx "2"))])
        (Term.hole "_")
        («term_<|_» `half_pos "<|" (Term.app `half_pos [`ε0]))])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_<|_»', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_<|_»', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_<|_» `half_pos "<|" (Term.app `half_pos [`ε0]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `half_pos [`ε0])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `ε0
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `half_pos
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 10 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 10, term))
      `half_pos
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 10, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 10, (some 10, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     («term_<|_» `half_pos "<|" (Term.app `half_pos [`ε0]))
     ")")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, term))
      (Term.app `Hs [`x (Term.proj `hx "." (fieldIdx "2"))])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.proj', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.proj', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.proj `hx "." (fieldIdx "2"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `hx
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `x
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `Hs
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023,
     term) <=? (some 1023, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.app `Hs [`x (Term.proj `hx "." (fieldIdx "2"))])
     ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (Term.proj
       (Term.app
        (Term.proj
         (Term.app `nhds_within_has_basis [`nhds_basis_closed_ball (Term.hole "_")])
         "."
         `tendsto_iff)
        [`nhds_basis_closed_ball])
       "."
       (fieldIdx "1"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.app
       (Term.proj
        (Term.app `nhds_within_has_basis [`nhds_basis_closed_ball (Term.hole "_")])
        "."
        `tendsto_iff)
       [`nhds_basis_closed_ball])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `nhds_basis_closed_ball
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (Term.proj
       (Term.app `nhds_within_has_basis [`nhds_basis_closed_ball (Term.hole "_")])
       "."
       `tendsto_iff)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.app `nhds_within_has_basis [`nhds_basis_closed_ball (Term.hole "_")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, term))
      `nhds_basis_closed_ball
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1023, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `nhds_within_has_basis
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.app `nhds_within_has_basis [`nhds_basis_closed_ball (Term.hole "_")])
     ")")
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.app
      (Term.proj
       (Term.paren
        "("
        (Term.app `nhds_within_has_basis [`nhds_basis_closed_ball (Term.hole "_")])
        ")")
       "."
       `tendsto_iff)
      [`nhds_basis_closed_ball])
     ")")
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (tactic__
       (cdotTk (patternIgnore (token.«· » "·")))
       [(Tactic.exact
         "exact"
         (Term.app
          `Ioc_mem_nhds_within_Ioi
          [(Term.anonymousCtor "⟨" [`le_rfl "," `one_half_pos] "⟩")]))])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.exact
       "exact"
       (Term.app
        `Ioc_mem_nhds_within_Ioi
        [(Term.anonymousCtor "⟨" [`le_rfl "," `one_half_pos] "⟩")]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `Ioc_mem_nhds_within_Ioi [(Term.anonymousCtor "⟨" [`le_rfl "," `one_half_pos] "⟩")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.anonymousCtor', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.anonymousCtor', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.anonymousCtor "⟨" [`le_rfl "," `one_half_pos] "⟩")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `one_half_pos
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `le_rfl
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `Ioc_mem_nhds_within_Ioi
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.refine'
       "refine'"
       (Term.app
        `eventually.and
        [(Term.hole "_") (Term.app `eventually.and [(Term.hole "_") (Term.hole "_")])]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       `eventually.and
       [(Term.hole "_") (Term.app `eventually.and [(Term.hole "_") (Term.hole "_")])])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `eventually.and [(Term.hole "_") (Term.hole "_")])
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
      `eventually.and
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.app `eventually.and [(Term.hole "_") (Term.hole "_")])
     ")")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `eventually.and
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, tactic) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Filter.Order.Filter.Basic.«term∀ᶠ_in_,_»
       "∀ᶠ"
       (Std.ExtendedBinder.extBinders (Std.ExtendedBinder.extBinder (Lean.binderIdent `δ) []))
       " in "
       (TopologicalSpace.Topology.Basic.nhds_within.gt
        "𝓝[>] "
        (Term.typeAscription "(" (num "0") ":" [(Data.Real.Basic.termℝ "ℝ")] ")"))
       ", "
       («term_∧_»
        («term_∈_»
         `δ
         "∈"
         (Term.app
          `Ioc
          [(Term.typeAscription "(" (num "0") ":" [(Data.Real.Basic.termℝ "ℝ")] ")")
           («term_/_» (num "1") "/" (num "2"))]))
        "∧"
        («term_∧_»
         (Term.forall
          "∀"
          [(Term.explicitBinder "(" [`y₁] [] [] ")")
           (Term.explicitBinder
            "("
            [(Term.hole "_")]
            [":" («term_∈_» `y₁ "∈" («term_∩_» (Term.app `closed_ball [`x `δ]) "∩" `I.Icc))]
            []
            ")")
           (Term.explicitBinder "(" [`y₂] [] [] ")")
           (Term.explicitBinder
            "("
            [(Term.hole "_")]
            [":" («term_∈_» `y₂ "∈" («term_∩_» (Term.app `closed_ball [`x `δ]) "∩" `I.Icc))]
            []
            ")")]
          []
          ","
          («term_≤_»
           (Analysis.Normed.Group.Basic.«term‖_‖»
            "‖"
            («term_-_» (Term.app `f [`y₁]) "-" (Term.app `f [`y₂]))
            "‖")
           "≤"
           («term_/_» `ε "/" (num "2"))))
         "∧"
         («term_≤_»
          («term_*_»
           («term_^_» («term_*_» (num "2") "*" `δ) "^" («term_+_» `n "+" (num "1")))
           "*"
           (Analysis.Normed.Group.Basic.«term‖_‖»
            "‖"
            (Term.app `f' [`x (Term.app `Pi.single [`i (num "1")])])
            "‖"))
          "≤"
          («term_/_» `ε "/" (num "2"))))))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_∧_»
       («term_∈_»
        `δ
        "∈"
        (Term.app
         `Ioc
         [(Term.typeAscription "(" (num "0") ":" [(Data.Real.Basic.termℝ "ℝ")] ")")
          («term_/_» (num "1") "/" (num "2"))]))
       "∧"
       («term_∧_»
        (Term.forall
         "∀"
         [(Term.explicitBinder "(" [`y₁] [] [] ")")
          (Term.explicitBinder
           "("
           [(Term.hole "_")]
           [":" («term_∈_» `y₁ "∈" («term_∩_» (Term.app `closed_ball [`x `δ]) "∩" `I.Icc))]
           []
           ")")
          (Term.explicitBinder "(" [`y₂] [] [] ")")
          (Term.explicitBinder
           "("
           [(Term.hole "_")]
           [":" («term_∈_» `y₂ "∈" («term_∩_» (Term.app `closed_ball [`x `δ]) "∩" `I.Icc))]
           []
           ")")]
         []
         ","
         («term_≤_»
          (Analysis.Normed.Group.Basic.«term‖_‖»
           "‖"
           («term_-_» (Term.app `f [`y₁]) "-" (Term.app `f [`y₂]))
           "‖")
          "≤"
          («term_/_» `ε "/" (num "2"))))
        "∧"
        («term_≤_»
         («term_*_»
          («term_^_» («term_*_» (num "2") "*" `δ) "^" («term_+_» `n "+" (num "1")))
          "*"
          (Analysis.Normed.Group.Basic.«term‖_‖»
           "‖"
           (Term.app `f' [`x (Term.app `Pi.single [`i (num "1")])])
           "‖"))
         "≤"
         («term_/_» `ε "/" (num "2")))))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_∧_»
       (Term.forall
        "∀"
        [(Term.explicitBinder "(" [`y₁] [] [] ")")
         (Term.explicitBinder
          "("
          [(Term.hole "_")]
          [":" («term_∈_» `y₁ "∈" («term_∩_» (Term.app `closed_ball [`x `δ]) "∩" `I.Icc))]
          []
          ")")
         (Term.explicitBinder "(" [`y₂] [] [] ")")
         (Term.explicitBinder
          "("
          [(Term.hole "_")]
          [":" («term_∈_» `y₂ "∈" («term_∩_» (Term.app `closed_ball [`x `δ]) "∩" `I.Icc))]
          []
          ")")]
        []
        ","
        («term_≤_»
         (Analysis.Normed.Group.Basic.«term‖_‖»
          "‖"
          («term_-_» (Term.app `f [`y₁]) "-" (Term.app `f [`y₂]))
          "‖")
         "≤"
         («term_/_» `ε "/" (num "2"))))
       "∧"
       («term_≤_»
        («term_*_»
         («term_^_» («term_*_» (num "2") "*" `δ) "^" («term_+_» `n "+" (num "1")))
         "*"
         (Analysis.Normed.Group.Basic.«term‖_‖»
          "‖"
          (Term.app `f' [`x (Term.app `Pi.single [`i (num "1")])])
          "‖"))
        "≤"
        («term_/_» `ε "/" (num "2"))))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_≤_»
       («term_*_»
        («term_^_» («term_*_» (num "2") "*" `δ) "^" («term_+_» `n "+" (num "1")))
        "*"
        (Analysis.Normed.Group.Basic.«term‖_‖»
         "‖"
         (Term.app `f' [`x (Term.app `Pi.single [`i (num "1")])])
         "‖"))
       "≤"
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
[PrettyPrinter.parenthesize] ...precedences are 51 >? 70, (some 71, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 50, term))
      («term_*_»
       («term_^_» («term_*_» (num "2") "*" `δ) "^" («term_+_» `n "+" (num "1")))
       "*"
       (Analysis.Normed.Group.Basic.«term‖_‖»
        "‖"
        (Term.app `f' [`x (Term.app `Pi.single [`i (num "1")])])
        "‖"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Analysis.Normed.Group.Basic.«term‖_‖»
       "‖"
       (Term.app `f' [`x (Term.app `Pi.single [`i (num "1")])])
       "‖")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `f' [`x (Term.app `Pi.single [`i (num "1")])])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `Pi.single [`i (num "1")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'num', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'num', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (num "1")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `i
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `Pi.single
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.app `Pi.single [`i (num "1")])
     ")")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `x
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `f'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 71 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 70, term))
      («term_^_» («term_*_» (num "2") "*" `δ) "^" («term_+_» `n "+" (num "1")))
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
      («term_*_» (num "2") "*" `δ)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `δ
[PrettyPrinter.parenthesize] ...precedences are 71 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 70, term))
      (num "2")
[PrettyPrinter.parenthesize] ...precedences are 70 >? 1024, (none, [anonymous]) <=? (some 70, term)
[PrettyPrinter.parenthesize] ...precedences are 81 >? 70, (some 71, term) <=? (some 80, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren "(" («term_*_» (num "2") "*" `δ) ")")
[PrettyPrinter.parenthesize] ...precedences are 70 >? 80, (some 80, term) <=? (some 70, term)
[PrettyPrinter.parenthesize] ...precedences are 51 >? 70, (some 71, term) <=? (some 50, term)
[PrettyPrinter.parenthesize] ...precedences are 35 >? 50, (some 51, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 35, term))
      (Term.forall
       "∀"
       [(Term.explicitBinder "(" [`y₁] [] [] ")")
        (Term.explicitBinder
         "("
         [(Term.hole "_")]
         [":" («term_∈_» `y₁ "∈" («term_∩_» (Term.app `closed_ball [`x `δ]) "∩" `I.Icc))]
         []
         ")")
        (Term.explicitBinder "(" [`y₂] [] [] ")")
        (Term.explicitBinder
         "("
         [(Term.hole "_")]
         [":" («term_∈_» `y₂ "∈" («term_∩_» (Term.app `closed_ball [`x `δ]) "∩" `I.Icc))]
         []
         ")")]
       []
       ","
       («term_≤_»
        (Analysis.Normed.Group.Basic.«term‖_‖»
         "‖"
         («term_-_» (Term.app `f [`y₁]) "-" (Term.app `f [`y₂]))
         "‖")
        "≤"
        («term_/_» `ε "/" (num "2"))))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_≤_»
       (Analysis.Normed.Group.Basic.«term‖_‖»
        "‖"
        («term_-_» (Term.app `f [`y₁]) "-" (Term.app `f [`y₂]))
        "‖")
       "≤"
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
[PrettyPrinter.parenthesize] ...precedences are 51 >? 70, (some 71, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 50, term))
      (Analysis.Normed.Group.Basic.«term‖_‖»
       "‖"
       («term_-_» (Term.app `f [`y₁]) "-" (Term.app `f [`y₂]))
       "‖")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_-_» (Term.app `f [`y₁]) "-" (Term.app `f [`y₂]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `f [`y₂])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `y₂
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `f
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 66 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 65, term))
      (Term.app `f [`y₁])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `y₁
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `f
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 65 >? 1022, (some 1023, term) <=? (some 65, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 65, (some 66, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1024, (none, [anonymous]) <=? (some 50, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 50, (some 51, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.explicitBinder', expected 'ident'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.explicitBinder', expected 'Lean.Parser.Term.hole'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_∈_» `y₂ "∈" («term_∩_» (Term.app `closed_ball [`x `δ]) "∩" `I.Icc))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_∩_» (Term.app `closed_ball [`x `δ]) "∩" `I.Icc)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `I.Icc
[PrettyPrinter.parenthesize] ...precedences are 71 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 70, term))
      (Term.app `closed_ball [`x `δ])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `δ
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `x
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `closed_ball
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 70 >? 1022, (some 1023, term) <=? (some 70, term)
[PrettyPrinter.parenthesize] ...precedences are 51 >? 70, (some 71, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 50, term))
      `y₂
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1024, (none, [anonymous]) <=? (some 50, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 50, (some 51, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'ident'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.explicitBinder', expected 'ident'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.explicitBinder', expected 'Lean.Parser.Term.hole'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.explicitBinder', expected 'ident'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.explicitBinder', expected 'Lean.Parser.Term.hole'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_∈_» `y₁ "∈" («term_∩_» (Term.app `closed_ball [`x `δ]) "∩" `I.Icc))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_∩_» (Term.app `closed_ball [`x `δ]) "∩" `I.Icc)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `I.Icc
[PrettyPrinter.parenthesize] ...precedences are 71 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 70, term))
      (Term.app `closed_ball [`x `δ])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `δ
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `x
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `closed_ball
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 70 >? 1022, (some 1023, term) <=? (some 70, term)
[PrettyPrinter.parenthesize] ...precedences are 51 >? 70, (some 71, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 50, term))
      `y₁
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1024, (none, [anonymous]) <=? (some 50, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 50, (some 51, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'ident'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.explicitBinder', expected 'ident'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.explicitBinder', expected 'Lean.Parser.Term.hole'
[PrettyPrinter.parenthesize] ...precedences are 36 >? 1022, (some 0, term) <=? (some 35, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.forall
      "∀"
      [(Term.explicitBinder "(" [`y₁] [] [] ")")
       (Term.explicitBinder
        "("
        [(Term.hole "_")]
        [":" («term_∈_» `y₁ "∈" («term_∩_» (Term.app `closed_ball [`x `δ]) "∩" `I.Icc))]
        []
        ")")
       (Term.explicitBinder "(" [`y₂] [] [] ")")
       (Term.explicitBinder
        "("
        [(Term.hole "_")]
        [":" («term_∈_» `y₂ "∈" («term_∩_» (Term.app `closed_ball [`x `δ]) "∩" `I.Icc))]
        []
        ")")]
      []
      ","
      («term_≤_»
       (Analysis.Normed.Group.Basic.«term‖_‖»
        "‖"
        («term_-_» (Term.app `f [`y₁]) "-" (Term.app `f [`y₂]))
        "‖")
       "≤"
       («term_/_» `ε "/" (num "2"))))
     ")")
[PrettyPrinter.parenthesize] ...precedences are 35 >? 35, (some 35, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 35, term))
      («term_∈_»
       `δ
       "∈"
       (Term.app
        `Ioc
        [(Term.typeAscription "(" (num "0") ":" [(Data.Real.Basic.termℝ "ℝ")] ")")
         («term_/_» (num "1") "/" (num "2"))]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       `Ioc
       [(Term.typeAscription "(" (num "0") ":" [(Data.Real.Basic.termℝ "ℝ")] ")")
        («term_/_» (num "1") "/" (num "2"))])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_/_»', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_/_»', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_/_» (num "1") "/" (num "2"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (num "2")
[PrettyPrinter.parenthesize] ...precedences are 71 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 70, term))
      (num "1")
[PrettyPrinter.parenthesize] ...precedences are 70 >? 1024, (none, [anonymous]) <=? (some 70, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 70, (some 71, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren "(" («term_/_» (num "1") "/" (num "2")) ")")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.typeAscription', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.typeAscription', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.typeAscription "(" (num "0") ":" [(Data.Real.Basic.termℝ "ℝ")] ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Data.Real.Basic.termℝ "ℝ")
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (num "0")
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `Ioc
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 50, term))
      `δ
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1024, (none, [anonymous]) <=? (some 50, term)
[PrettyPrinter.parenthesize] ...precedences are 36 >? 50, (some 51, term) <=? (some 35, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 35, (some 35, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (TopologicalSpace.Topology.Basic.nhds_within.gt
       "𝓝[>] "
       (Term.typeAscription "(" (num "0") ":" [(Data.Real.Basic.termℝ "ℝ")] ")"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.typeAscription "(" (num "0") ":" [(Data.Real.Basic.termℝ "ℝ")] ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Data.Real.Basic.termℝ "ℝ")
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (num "0")
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 100 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 100, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.intro "intro" [`c `x `hx `ε `ε0])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `ε0
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `ε
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `hx
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `x
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `c
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (tactic__
       (cdotTk (patternIgnore (token.«· » "·")))
       [(Tactic.exact
         "exact"
         (Term.fun "fun" (Term.basicFun [`J] [] "=>" `Ennreal.to_real_nonneg)))])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.exact "exact" (Term.fun "fun" (Term.basicFun [`J] [] "=>" `Ennreal.to_real_nonneg)))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.fun "fun" (Term.basicFun [`J] [] "=>" `Ennreal.to_real_nonneg))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `Ennreal.to_real_nonneg
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.strictImplicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.implicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.instBinder'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `J
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (tactic__
       (cdotTk (patternIgnore (token.«· » "·")))
       [(Tactic.exact
         "exact"
         (Term.app
          (Term.proj
           (Term.proj
            (Term.typeAscription
             "("
             `volume
             ":"
             [(Term.app
               `Measure
               [(BoxIntegral.Analysis.BoxIntegral.DivergenceTheorem.«termℝⁿ⁺¹» "ℝⁿ⁺¹")])]
             ")")
            "."
            `toBoxAdditive)
           "."
           `restrict)
          [(Term.hole "_") `le_top]))])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.exact
       "exact"
       (Term.app
        (Term.proj
         (Term.proj
          (Term.typeAscription
           "("
           `volume
           ":"
           [(Term.app
             `Measure
             [(BoxIntegral.Analysis.BoxIntegral.DivergenceTheorem.«termℝⁿ⁺¹» "ℝⁿ⁺¹")])]
           ")")
          "."
          `toBoxAdditive)
         "."
         `restrict)
        [(Term.hole "_") `le_top]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       (Term.proj
        (Term.proj
         (Term.typeAscription
          "("
          `volume
          ":"
          [(Term.app
            `Measure
            [(BoxIntegral.Analysis.BoxIntegral.DivergenceTheorem.«termℝⁿ⁺¹» "ℝⁿ⁺¹")])]
          ")")
         "."
         `toBoxAdditive)
        "."
        `restrict)
       [(Term.hole "_") `le_top])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `le_top
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (Term.proj
       (Term.proj
        (Term.typeAscription
         "("
         `volume
         ":"
         [(Term.app
           `Measure
           [(BoxIntegral.Analysis.BoxIntegral.DivergenceTheorem.«termℝⁿ⁺¹» "ℝⁿ⁺¹")])]
         ")")
        "."
        `toBoxAdditive)
       "."
       `restrict)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.proj
       (Term.typeAscription
        "("
        `volume
        ":"
        [(Term.app
          `Measure
          [(BoxIntegral.Analysis.BoxIntegral.DivergenceTheorem.«termℝⁿ⁺¹» "ℝⁿ⁺¹")])]
        ")")
       "."
       `toBoxAdditive)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.typeAscription
       "("
       `volume
       ":"
       [(Term.app
         `Measure
         [(BoxIntegral.Analysis.BoxIntegral.DivergenceTheorem.«termℝⁿ⁺¹» "ℝⁿ⁺¹")])]
       ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `Measure [(BoxIntegral.Analysis.BoxIntegral.DivergenceTheorem.«termℝⁿ⁺¹» "ℝⁿ⁺¹")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'BoxIntegral.Analysis.BoxIntegral.DivergenceTheorem.«termℝⁿ⁺¹»', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'BoxIntegral.Analysis.BoxIntegral.DivergenceTheorem.«termℝⁿ⁺¹»', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (BoxIntegral.Analysis.BoxIntegral.DivergenceTheorem.«termℝⁿ⁺¹» "ℝⁿ⁺¹")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'BoxIntegral.Analysis.BoxIntegral.DivergenceTheorem.«termℝⁿ⁺¹»', expected 'BoxIntegral.Analysis.BoxIntegral.DivergenceTheorem.termℝⁿ⁺¹._@.Analysis.BoxIntegral.DivergenceTheorem._hyg.52'
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
    If `f : ℝⁿ⁺¹ → E` is differentiable on a closed rectangular box `I` with derivative `f'`, then
    the partial derivative `λ x, f' x (pi.single i 1)` is Henstock-Kurzweil integrable with integral
    equal to the difference of integrals of `f` over the faces `x i = I.upper i` and `x i = I.lower i`.
    
    More precisely, we use a non-standard generalization of the Henstock-Kurzweil integral and
    we allow `f` to be non-differentiable (but still continuous) at a countable set of points.
    
    TODO: If `n > 0`, then the condition at `x ∈ s` can be replaced by a much weaker estimate but this
    requires either better integrability theorems, or usage of a filter depending on the countable set
    `s` (we need to ensure that none of the faces of a partition contain a point from `s`). -/
  theorem
    hasIntegralGPPderiv
    ( f : ℝⁿ⁺¹ → E )
        ( f' : ℝⁿ⁺¹ → ℝⁿ⁺¹ →L[ ℝ ] E )
        ( s : Set ℝⁿ⁺¹ )
        ( hs : s . Countable )
        ( Hs : ∀ x ∈ s , ContinuousWithinAt f I . IccCat x )
        ( Hd : ∀ x ∈ I . IccCat \ s , HasFderivWithinAt f f' x I . IccCat x )
        ( i : Fin n + 1 )
      :
        HasIntegral .{ 0 , u , u }
          I
            gP
            fun x => f' x Pi.single i 1
            BoxAdditiveMap.volume
            integral .{ 0 , u , u }
                I . face i gP fun x => f i . insertNth I . upper i x BoxAdditiveMap.volume
              -
              integral .{ 0 , u , u }
                I . face i gP fun x => f i . insertNth I . lower i x BoxAdditiveMap.volume
    :=
      by
        have
            Hc
              : ContinuousOn f I.Icc
              :=
              by
                intro x hx
                  by_cases hxs : x ∈ s
                  exacts [ Hs x hxs , Hd x ⟨ hx , hxs ⟩ . ContinuousWithinAt ]
          set
            fI
              : ℝ → box Fin n → E
              :=
              fun
                y J
                  =>
                  integral .{ 0 , u , u } J GP fun x => f i.insert_nth y x box_additive_map.volume
          set
            fb
              : Icc I.lower i I.upper i → Fin n →ᵇᵃ[ ↑ I.face i ] E
              :=
              fun
                x
                  =>
                  integrable_of_continuous_on GP box.continuous_on_face_Icc Hc x . 2 volume
                    .
                    toBoxAdditive
          set
            F : Fin n + 1 →ᵇᵃ[ I ] E := box_additive_map.upper_sub_lower I i fI fb fun x hx J => rfl
          change has_integral I GP fun x => f' x Pi.single i 1 _ F I
          refine' has_integral_of_le_Henstock_of_forall_is_o GP_le _ _ _ s hs _ _
          · exact ( volume : Measure ℝⁿ⁺¹ ) . toBoxAdditive . restrict _ le_top
          · exact fun J => Ennreal.to_real_nonneg
          ·
            intro c x hx ε ε0
              have
                :
                    ∀ᶠ
                      δ
                      in
                      𝓝[>] ( 0 : ℝ )
                      ,
                      δ ∈ Ioc ( 0 : ℝ ) 1 / 2
                        ∧
                        ∀
                            ( y₁ )
                              ( _ : y₁ ∈ closed_ball x δ ∩ I.Icc )
                              ( y₂ )
                              ( _ : y₂ ∈ closed_ball x δ ∩ I.Icc )
                            ,
                            ‖ f y₁ - f y₂ ‖ ≤ ε / 2
                          ∧
                          2 * δ ^ n + 1 * ‖ f' x Pi.single i 1 ‖ ≤ ε / 2
                  :=
                  by
                    refine' eventually.and _ eventually.and _ _
                      · exact Ioc_mem_nhds_within_Ioi ⟨ le_rfl , one_half_pos ⟩
                      ·
                        rcases
                            nhds_within_has_basis nhds_basis_closed_ball _ . tendsto_iff
                                  nhds_basis_closed_ball
                                .
                                1
                              Hs x hx . 2 _ half_pos <| half_pos ε0
                            with ⟨ δ₁ , δ₁0 , hδ₁ ⟩
                          filter_upwards
                            [ Ioc_mem_nhds_within_Ioi ⟨ le_rfl , δ₁0 ⟩ ]
                            with δ hδ y₁ hy₁ y₂ hy₂
                          have
                            : closed_ball x δ ∩ I.Icc ⊆ closed_ball x δ₁ ∩ I.Icc
                              :=
                              inter_subset_inter_left _ closed_ball_subset_closed_ball hδ . 2
                          rw [ ← dist_eq_norm ]
                          calc
                            dist f y₁ f y₂ ≤ dist f y₁ f x + dist f y₂ f x
                              :=
                              dist_triangle_right _ _ _
                            _ ≤ ε / 2 / 2 + ε / 2 / 2
                                :=
                                add_le_add hδ₁ _ <| this hy₁ hδ₁ _ <| this hy₂
                              _ = ε / 2 := add_halves _
                      ·
                        have
                            :
                                ContinuousWithinAt
                                  fun δ => 2 * δ ^ n + 1 * ‖ f' x Pi.single i 1 ‖ Ioi ( 0 : ℝ ) 0
                              :=
                              continuous_within_at_id.const_mul _ . pow _ . mul_const _
                          refine' this.eventually ge_mem_nhds _
                          simpa using half_pos ε0
              rcases this.exists with ⟨ δ , ⟨ hδ0 , hδ12 ⟩ , hdfδ , hδ ⟩
              refine' ⟨ δ , hδ0 , fun J hJI hJδ hxJ hJc => add_halves ε ▸ _ ⟩
              have
                Hl : J.lower i ∈ Icc J.lower i J.upper i := Set.left_mem_Icc . 2 J.lower_le_upper i
              have
                Hu : J.upper i ∈ Icc J.lower i J.upper i := Set.right_mem_Icc . 2 J.lower_le_upper i
              have
                Hi
                  :
                    ∀
                      x
                      ∈ Icc J.lower i J.upper i
                      ,
                      Integrable .{ 0 , u , u }
                        J.face i GP fun y => f i.insert_nth x y box_additive_map.volume
                  :=
                  fun
                    x hx
                      =>
                      integrable_of_continuous_on
                        _ box.continuous_on_face_Icc Hc.mono <| box.le_iff_Icc . 1 hJI hx volume
              have hJδ' : J.Icc ⊆ closed_ball x δ ∩ I.Icc := subset_inter hJδ box.le_iff_Icc . 1 hJI
              have
                Hmaps
                  :
                    ∀
                      z
                      ∈ Icc J.lower i J.upper i
                      ,
                      maps_to i.insert_nth z J.face i . IccCat closed_ball x δ ∩ I.Icc
                  :=
                  fun z hz => J.maps_to_insert_nth_face_Icc hz . mono subset.rfl hJδ'
              simp only [ dist_eq_norm , F , fI ]
              dsimp
              rw [ ← integral_sub Hi _ Hu Hi _ Hl ]
              refine' norm_sub_le _ _ . trans add_le_add _ _
              ·
                simp_rw [ box_additive_map.volume_apply , norm_smul , Real.norm_eq_abs , abs_prod ]
                  refine' mul_le_mul_of_nonneg_right _ <| norm_nonneg _ . trans hδ
                  have
                    : ∀ j , | J.upper j - J.lower j | ≤ 2 * δ
                      :=
                      by
                        intro j
                          calc
                            dist J.upper j J.lower j ≤ dist J.upper J.lower := dist_le_pi_dist _ _ _
                            _ ≤ dist J.upper x + dist J.lower x := dist_triangle_right _ _ _
                              _ ≤ δ + δ := add_le_add hJδ J.upper_mem_Icc hJδ J.lower_mem_Icc
                              _ = 2 * δ := two_mul δ . symm
                  calc
                    ∏ j , | J.upper j - J.lower j | ≤ ∏ j : Fin n + 1 , 2 * δ
                      :=
                      prod_le_prod fun _ _ => abs_nonneg _ fun j hj => this j
                    _ = 2 * δ ^ n + 1 := by simp
              ·
                refine'
                    norm_integral_le_of_le_const fun y hy => hdfδ _ Hmaps _ Hu hy _ Hmaps _ Hl hy _
                        .
                        trans
                      _
                  refine' mul_le_mul_of_nonneg_right _ half_pos ε0 . le . trans_eq one_mul _
                  rw [ box.coe_eq_pi , Real.volume_pi_Ioc_to_real box.lower_le_upper _ ]
                  refine'
                    prod_le_one fun _ _ => sub_nonneg . 2 <| box.lower_le_upper _ _ fun j hj => _
                  calc
                    J.upper i.succ_above j - J.lower i.succ_above j
                        ≤
                        dist J.upper i.succ_above j J.lower i.succ_above j
                      :=
                      le_abs_self _
                    _ ≤ dist J.upper J.lower := dist_le_pi_dist J.upper J.lower i.succ_above j
                      _ ≤ dist J.upper x + dist J.lower x := dist_triangle_right _ _ _
                      _ ≤ δ + δ := add_le_add hJδ J.upper_mem_Icc hJδ J.lower_mem_Icc
                      _ ≤ 1 / 2 + 1 / 2 := add_le_add hδ12 hδ12
                      _ = 1 := add_halves 1
          ·
            intro c x hx ε ε0
              rcases exists_pos_mul_lt ε0 2 * c with ⟨ ε' , ε'0 , hlt ⟩
              rcases
                nhds_within_has_basis nhds_basis_closed_ball _ . mem_iff . 1 Hd x hx . def ε'0
                with ⟨ δ , δ0 , Hδ ⟩
              refine' ⟨ δ , δ0 , fun J hle hJδ hxJ hJc => _ ⟩
              simp only [ box_additive_map.volume_apply , box.volume_apply , dist_eq_norm ]
              refine'
                norm_volume_sub_integral_face_upper_sub_lower_smul_le
                      _ Hc.mono <| box.le_iff_Icc . 1 hle hxJ ε'0 fun y hy => Hδ _ hJc rfl
                    .
                    trans
                  _
              · exact ⟨ hJδ hy , box.le_iff_Icc . 1 hle hy ⟩
              ·
                rw [ mul_right_comm ( 2 : ℝ ) , ← box.volume_apply ]
                  exact mul_le_mul_of_nonneg_right hlt.le Ennreal.to_real_nonneg
#align box_integral.has_integral_GP_pderiv BoxIntegral.hasIntegralGPPderiv

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers
      [(Command.docComment
        "/--"
        "Divergence theorem for a Henstock-Kurzweil style integral.\n\nIf `f : ℝⁿ⁺¹ → Eⁿ⁺¹` is differentiable on a closed rectangular box `I` with derivative `f'`, then\nthe divergence `∑ i, f' x (pi.single i 1) i` is Henstock-Kurzweil integrable with integral equal to\nthe sum of integrals of `f` over the faces of `I` taken with appropriate signs.\n\nMore precisely, we use a non-standard generalization of the Henstock-Kurzweil integral and\nwe allow `f` to be non-differentiable (but still continuous) at a countable set of points. -/")]
      []
      []
      []
      []
      [])
     (Command.theorem
      "theorem"
      (Command.declId `hasIntegralGPDivergenceOfForallHasDerivWithinAt [])
      (Command.declSig
       [(Term.explicitBinder
         "("
         [`f]
         [":"
          (Term.arrow
           (BoxIntegral.Analysis.BoxIntegral.DivergenceTheorem.«termℝⁿ⁺¹» "ℝⁿ⁺¹")
           "→"
           (BoxIntegral.Analysis.BoxIntegral.DivergenceTheorem.«termEⁿ⁺¹» "Eⁿ⁺¹"))]
         []
         ")")
        (Term.explicitBinder
         "("
         [`f']
         [":"
          (Term.arrow
           (BoxIntegral.Analysis.BoxIntegral.DivergenceTheorem.«termℝⁿ⁺¹» "ℝⁿ⁺¹")
           "→"
           (Topology.Algebra.Module.Basic.«term_→L[_]_»
            (BoxIntegral.Analysis.BoxIntegral.DivergenceTheorem.«termℝⁿ⁺¹» "ℝⁿ⁺¹")
            " →L["
            (Data.Real.Basic.termℝ "ℝ")
            "] "
            (BoxIntegral.Analysis.BoxIntegral.DivergenceTheorem.«termEⁿ⁺¹» "Eⁿ⁺¹")))]
         []
         ")")
        (Term.explicitBinder
         "("
         [`s]
         [":"
          (Term.app `Set [(BoxIntegral.Analysis.BoxIntegral.DivergenceTheorem.«termℝⁿ⁺¹» "ℝⁿ⁺¹")])]
         []
         ")")
        (Term.explicitBinder "(" [`hs] [":" (Term.proj `s "." `Countable)] [] ")")
        (Term.explicitBinder
         "("
         [`Hs]
         [":"
          (Std.ExtendedBinder.«term∀__,_»
           "∀"
           (Lean.binderIdent `x)
           («binderTerm∈_» "∈" `s)
           ","
           (Term.app `ContinuousWithinAt [`f (Term.proj `I "." `IccCat) `x]))]
         []
         ")")
        (Term.explicitBinder
         "("
         [`Hd]
         [":"
          (Std.ExtendedBinder.«term∀__,_»
           "∀"
           (Lean.binderIdent `x)
           («binderTerm∈_» "∈" («term_\_» (Term.proj `I "." `IccCat) "\\" `s))
           ","
           (Term.app `HasFderivWithinAt [`f (Term.app `f' [`x]) (Term.proj `I "." `IccCat) `x]))]
         []
         ")")]
       (Term.typeSpec
        ":"
        (Term.app
         (Term.explicitUniv `HasIntegral ".{" [(num "0") "," `u "," `u] "}")
         [`I
          `gP
          (Term.fun
           "fun"
           (Term.basicFun
            [`x]
            []
            "=>"
            (BigOperators.Algebra.BigOperators.Basic.finset.sum_univ
             "∑"
             (Std.ExtendedBinder.extBinders (Std.ExtendedBinder.extBinder (Lean.binderIdent `i) []))
             ", "
             (Term.app `f' [`x (Term.app `Pi.single [`i (num "1")]) `i]))))
          `BoxAdditiveMap.volume
          (BigOperators.Algebra.BigOperators.Basic.finset.sum_univ
           "∑"
           (Std.ExtendedBinder.extBinders (Std.ExtendedBinder.extBinder (Lean.binderIdent `i) []))
           ", "
           («term_-_»
            (Term.app
             (Term.explicitUniv `integral ".{" [(num "0") "," `u "," `u] "}")
             [(Term.app (Term.proj `I "." `face) [`i])
              `gP
              (Term.fun
               "fun"
               (Term.basicFun
                [`x]
                []
                "=>"
                (Term.app
                 `f
                 [(Term.app
                   (Term.proj `i "." `insertNth)
                   [(Term.app (Term.proj `I "." `upper) [`i]) `x])
                  `i])))
              `BoxAdditiveMap.volume])
            "-"
            (Term.app
             (Term.explicitUniv `integral ".{" [(num "0") "," `u "," `u] "}")
             [(Term.app (Term.proj `I "." `face) [`i])
              `gP
              (Term.fun
               "fun"
               (Term.basicFun
                [`x]
                []
                "=>"
                (Term.app
                 `f
                 [(Term.app
                   (Term.proj `i "." `insertNth)
                   [(Term.app (Term.proj `I "." `lower) [`i]) `x])
                  `i])))
              `BoxAdditiveMap.volume])))])))
      (Command.declValSimple
       ":="
       (Term.byTactic
        "by"
        (Tactic.tacticSeq
         (Tactic.tacticSeq1Indented
          [(Tactic.refine'
            "refine'"
            (Term.app
             `has_integral_sum
             [(Term.fun "fun" (Term.basicFun [`i `hi] [] "=>" (Term.hole "_")))]))
           ";"
           (Tactic.clear "clear" [`hi])
           []
           (Tactic.simp
            "simp"
            []
            []
            ["only"]
            ["["
             [(Tactic.simpLemma [] [] `has_fderiv_within_at_pi')
              ","
              (Tactic.simpLemma [] [] `continuous_within_at_pi)]
             "]"]
            [(Tactic.location "at" (Tactic.locationHyp [`Hd `Hs] []))])
           []
           (convert
            "convert"
            []
            (Term.app
             `has_integral_GP_pderiv
             [`I
              (Term.hole "_")
              (Term.hole "_")
              `s
              `hs
              (Term.fun "fun" (Term.basicFun [`x `hx] [] "=>" (Term.app `Hs [`x `hx `i])))
              (Term.fun "fun" (Term.basicFun [`x `hx] [] "=>" (Term.app `Hd [`x `hx `i])))
              `i])
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
         [(Tactic.refine'
           "refine'"
           (Term.app
            `has_integral_sum
            [(Term.fun "fun" (Term.basicFun [`i `hi] [] "=>" (Term.hole "_")))]))
          ";"
          (Tactic.clear "clear" [`hi])
          []
          (Tactic.simp
           "simp"
           []
           []
           ["only"]
           ["["
            [(Tactic.simpLemma [] [] `has_fderiv_within_at_pi')
             ","
             (Tactic.simpLemma [] [] `continuous_within_at_pi)]
            "]"]
           [(Tactic.location "at" (Tactic.locationHyp [`Hd `Hs] []))])
          []
          (convert
           "convert"
           []
           (Term.app
            `has_integral_GP_pderiv
            [`I
             (Term.hole "_")
             (Term.hole "_")
             `s
             `hs
             (Term.fun "fun" (Term.basicFun [`x `hx] [] "=>" (Term.app `Hs [`x `hx `i])))
             (Term.fun "fun" (Term.basicFun [`x `hx] [] "=>" (Term.app `Hd [`x `hx `i])))
             `i])
           [])])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (convert
       "convert"
       []
       (Term.app
        `has_integral_GP_pderiv
        [`I
         (Term.hole "_")
         (Term.hole "_")
         `s
         `hs
         (Term.fun "fun" (Term.basicFun [`x `hx] [] "=>" (Term.app `Hs [`x `hx `i])))
         (Term.fun "fun" (Term.basicFun [`x `hx] [] "=>" (Term.app `Hd [`x `hx `i])))
         `i])
       [])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       `has_integral_GP_pderiv
       [`I
        (Term.hole "_")
        (Term.hole "_")
        `s
        `hs
        (Term.fun "fun" (Term.basicFun [`x `hx] [] "=>" (Term.app `Hs [`x `hx `i])))
        (Term.fun "fun" (Term.basicFun [`x `hx] [] "=>" (Term.app `Hd [`x `hx `i])))
        `i])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `i
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.fun "fun" (Term.basicFun [`x `hx] [] "=>" (Term.app `Hd [`x `hx `i])))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `Hd [`x `hx `i])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `i
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `hx
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `x
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `Hd
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.strictImplicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.implicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.instBinder'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `hx
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.strictImplicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.implicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.instBinder'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `x
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (some 0, term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.fun "fun" (Term.basicFun [`x `hx] [] "=>" (Term.app `Hd [`x `hx `i])))
     ")")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.fun "fun" (Term.basicFun [`x `hx] [] "=>" (Term.app `Hs [`x `hx `i])))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `Hs [`x `hx `i])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `i
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `hx
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `x
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `Hs
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.strictImplicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.implicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.instBinder'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `hx
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.strictImplicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.implicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.instBinder'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `x
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (some 0, term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.fun "fun" (Term.basicFun [`x `hx] [] "=>" (Term.app `Hs [`x `hx `i])))
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
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, term))
      `I
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1023, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `has_integral_GP_pderiv
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
        [(Tactic.simpLemma [] [] `has_fderiv_within_at_pi')
         ","
         (Tactic.simpLemma [] [] `continuous_within_at_pi)]
        "]"]
       [(Tactic.location "at" (Tactic.locationHyp [`Hd `Hs] []))])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.locationHyp', expected 'Lean.Parser.Tactic.locationWildcard'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `Hs
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `Hd
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `continuous_within_at_pi
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `has_fderiv_within_at_pi'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.clear "clear" [`hi])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `hi
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.refine'
       "refine'"
       (Term.app
        `has_integral_sum
        [(Term.fun "fun" (Term.basicFun [`i `hi] [] "=>" (Term.hole "_")))]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       `has_integral_sum
       [(Term.fun "fun" (Term.basicFun [`i `hi] [] "=>" (Term.hole "_")))])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.fun "fun" (Term.basicFun [`i `hi] [] "=>" (Term.hole "_")))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.strictImplicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.implicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.instBinder'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `hi
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
      `has_integral_sum
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, tactic) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
      (Term.app
       (Term.explicitUniv `HasIntegral ".{" [(num "0") "," `u "," `u] "}")
       [`I
        `gP
        (Term.fun
         "fun"
         (Term.basicFun
          [`x]
          []
          "=>"
          (BigOperators.Algebra.BigOperators.Basic.finset.sum_univ
           "∑"
           (Std.ExtendedBinder.extBinders (Std.ExtendedBinder.extBinder (Lean.binderIdent `i) []))
           ", "
           (Term.app `f' [`x (Term.app `Pi.single [`i (num "1")]) `i]))))
        `BoxAdditiveMap.volume
        (BigOperators.Algebra.BigOperators.Basic.finset.sum_univ
         "∑"
         (Std.ExtendedBinder.extBinders (Std.ExtendedBinder.extBinder (Lean.binderIdent `i) []))
         ", "
         («term_-_»
          (Term.app
           (Term.explicitUniv `integral ".{" [(num "0") "," `u "," `u] "}")
           [(Term.app (Term.proj `I "." `face) [`i])
            `gP
            (Term.fun
             "fun"
             (Term.basicFun
              [`x]
              []
              "=>"
              (Term.app
               `f
               [(Term.app
                 (Term.proj `i "." `insertNth)
                 [(Term.app (Term.proj `I "." `upper) [`i]) `x])
                `i])))
            `BoxAdditiveMap.volume])
          "-"
          (Term.app
           (Term.explicitUniv `integral ".{" [(num "0") "," `u "," `u] "}")
           [(Term.app (Term.proj `I "." `face) [`i])
            `gP
            (Term.fun
             "fun"
             (Term.basicFun
              [`x]
              []
              "=>"
              (Term.app
               `f
               [(Term.app
                 (Term.proj `i "." `insertNth)
                 [(Term.app (Term.proj `I "." `lower) [`i]) `x])
                `i])))
            `BoxAdditiveMap.volume])))])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'BigOperators.Algebra.BigOperators.Basic.finset.sum_univ', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'BigOperators.Algebra.BigOperators.Basic.finset.sum_univ', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (BigOperators.Algebra.BigOperators.Basic.finset.sum_univ
       "∑"
       (Std.ExtendedBinder.extBinders (Std.ExtendedBinder.extBinder (Lean.binderIdent `i) []))
       ", "
       («term_-_»
        (Term.app
         (Term.explicitUniv `integral ".{" [(num "0") "," `u "," `u] "}")
         [(Term.app (Term.proj `I "." `face) [`i])
          `gP
          (Term.fun
           "fun"
           (Term.basicFun
            [`x]
            []
            "=>"
            (Term.app
             `f
             [(Term.app
               (Term.proj `i "." `insertNth)
               [(Term.app (Term.proj `I "." `upper) [`i]) `x])
              `i])))
          `BoxAdditiveMap.volume])
        "-"
        (Term.app
         (Term.explicitUniv `integral ".{" [(num "0") "," `u "," `u] "}")
         [(Term.app (Term.proj `I "." `face) [`i])
          `gP
          (Term.fun
           "fun"
           (Term.basicFun
            [`x]
            []
            "=>"
            (Term.app
             `f
             [(Term.app
               (Term.proj `i "." `insertNth)
               [(Term.app (Term.proj `I "." `lower) [`i]) `x])
              `i])))
          `BoxAdditiveMap.volume])))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_-_»
       (Term.app
        (Term.explicitUniv `integral ".{" [(num "0") "," `u "," `u] "}")
        [(Term.app (Term.proj `I "." `face) [`i])
         `gP
         (Term.fun
          "fun"
          (Term.basicFun
           [`x]
           []
           "=>"
           (Term.app
            `f
            [(Term.app (Term.proj `i "." `insertNth) [(Term.app (Term.proj `I "." `upper) [`i]) `x])
             `i])))
         `BoxAdditiveMap.volume])
       "-"
       (Term.app
        (Term.explicitUniv `integral ".{" [(num "0") "," `u "," `u] "}")
        [(Term.app (Term.proj `I "." `face) [`i])
         `gP
         (Term.fun
          "fun"
          (Term.basicFun
           [`x]
           []
           "=>"
           (Term.app
            `f
            [(Term.app (Term.proj `i "." `insertNth) [(Term.app (Term.proj `I "." `lower) [`i]) `x])
             `i])))
         `BoxAdditiveMap.volume]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       (Term.explicitUniv `integral ".{" [(num "0") "," `u "," `u] "}")
       [(Term.app (Term.proj `I "." `face) [`i])
        `gP
        (Term.fun
         "fun"
         (Term.basicFun
          [`x]
          []
          "=>"
          (Term.app
           `f
           [(Term.app (Term.proj `i "." `insertNth) [(Term.app (Term.proj `I "." `lower) [`i]) `x])
            `i])))
        `BoxAdditiveMap.volume])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `BoxAdditiveMap.volume
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
        (Term.app
         `f
         [(Term.app (Term.proj `i "." `insertNth) [(Term.app (Term.proj `I "." `lower) [`i]) `x])
          `i])))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       `f
       [(Term.app (Term.proj `i "." `insertNth) [(Term.app (Term.proj `I "." `lower) [`i]) `x]) `i])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `i
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.app (Term.proj `i "." `insertNth) [(Term.app (Term.proj `I "." `lower) [`i]) `x])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `x
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.app (Term.proj `I "." `lower) [`i])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `i
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (Term.proj `I "." `lower)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `I
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023,
     term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.app (Term.proj `I "." `lower) [`i])
     ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (Term.proj `i "." `insertNth)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `i
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023,
     term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.app
      (Term.proj `i "." `insertNth)
      [(Term.paren "(" (Term.app (Term.proj `I "." `lower) [`i]) ")") `x])
     ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `f
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
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (some 0, term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.fun
      "fun"
      (Term.basicFun
       [`x]
       []
       "=>"
       (Term.app
        `f
        [(Term.paren
          "("
          (Term.app
           (Term.proj `i "." `insertNth)
           [(Term.paren "(" (Term.app (Term.proj `I "." `lower) [`i]) ")") `x])
          ")")
         `i])))
     ")")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `gP
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.app (Term.proj `I "." `face) [`i])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `i
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (Term.proj `I "." `face)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `I
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023,
     term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.app (Term.proj `I "." `face) [`i])
     ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (Term.explicitUniv `integral ".{" [(num "0") "," `u "," `u] "}")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `u
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `u
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (num "0")
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `integral
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 66 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 65, term))
      (Term.app
       (Term.explicitUniv `integral ".{" [(num "0") "," `u "," `u] "}")
       [(Term.app (Term.proj `I "." `face) [`i])
        `gP
        (Term.fun
         "fun"
         (Term.basicFun
          [`x]
          []
          "=>"
          (Term.app
           `f
           [(Term.app (Term.proj `i "." `insertNth) [(Term.app (Term.proj `I "." `upper) [`i]) `x])
            `i])))
        `BoxAdditiveMap.volume])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `BoxAdditiveMap.volume
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
        (Term.app
         `f
         [(Term.app (Term.proj `i "." `insertNth) [(Term.app (Term.proj `I "." `upper) [`i]) `x])
          `i])))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       `f
       [(Term.app (Term.proj `i "." `insertNth) [(Term.app (Term.proj `I "." `upper) [`i]) `x]) `i])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `i
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.app (Term.proj `i "." `insertNth) [(Term.app (Term.proj `I "." `upper) [`i]) `x])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `x
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.app (Term.proj `I "." `upper) [`i])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `i
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (Term.proj `I "." `upper)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `I
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023,
     term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.app (Term.proj `I "." `upper) [`i])
     ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (Term.proj `i "." `insertNth)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `i
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023,
     term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.app
      (Term.proj `i "." `insertNth)
      [(Term.paren "(" (Term.app (Term.proj `I "." `upper) [`i]) ")") `x])
     ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `f
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
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (some 0, term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.fun
      "fun"
      (Term.basicFun
       [`x]
       []
       "=>"
       (Term.app
        `f
        [(Term.paren
          "("
          (Term.app
           (Term.proj `i "." `insertNth)
           [(Term.paren "(" (Term.app (Term.proj `I "." `upper) [`i]) ")") `x])
          ")")
         `i])))
     ")")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `gP
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.app (Term.proj `I "." `face) [`i])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `i
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (Term.proj `I "." `face)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `I
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023,
     term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.app (Term.proj `I "." `face) [`i])
     ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (Term.explicitUniv `integral ".{" [(num "0") "," `u "," `u] "}")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `u
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `u
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (num "0")
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `integral
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 65 >? 1022, (some 1023, term) <=? (some 65, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 65, (some 66, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (BigOperators.Algebra.BigOperators.Basic.finset.sum_univ
      "∑"
      (Std.ExtendedBinder.extBinders (Std.ExtendedBinder.extBinder (Lean.binderIdent `i) []))
      ", "
      («term_-_»
       (Term.app
        (Term.explicitUniv `integral ".{" [(num "0") "," `u "," `u] "}")
        [(Term.paren "(" (Term.app (Term.proj `I "." `face) [`i]) ")")
         `gP
         (Term.paren
          "("
          (Term.fun
           "fun"
           (Term.basicFun
            [`x]
            []
            "=>"
            (Term.app
             `f
             [(Term.paren
               "("
               (Term.app
                (Term.proj `i "." `insertNth)
                [(Term.paren "(" (Term.app (Term.proj `I "." `upper) [`i]) ")") `x])
               ")")
              `i])))
          ")")
         `BoxAdditiveMap.volume])
       "-"
       (Term.app
        (Term.explicitUniv `integral ".{" [(num "0") "," `u "," `u] "}")
        [(Term.paren "(" (Term.app (Term.proj `I "." `face) [`i]) ")")
         `gP
         (Term.paren
          "("
          (Term.fun
           "fun"
           (Term.basicFun
            [`x]
            []
            "=>"
            (Term.app
             `f
             [(Term.paren
               "("
               (Term.app
                (Term.proj `i "." `insertNth)
                [(Term.paren "(" (Term.app (Term.proj `I "." `lower) [`i]) ")") `x])
               ")")
              `i])))
          ")")
         `BoxAdditiveMap.volume])))
     ")")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `BoxAdditiveMap.volume
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.fun
       "fun"
       (Term.basicFun
        [`x]
        []
        "=>"
        (BigOperators.Algebra.BigOperators.Basic.finset.sum_univ
         "∑"
         (Std.ExtendedBinder.extBinders (Std.ExtendedBinder.extBinder (Lean.binderIdent `i) []))
         ", "
         (Term.app `f' [`x (Term.app `Pi.single [`i (num "1")]) `i]))))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (BigOperators.Algebra.BigOperators.Basic.finset.sum_univ
       "∑"
       (Std.ExtendedBinder.extBinders (Std.ExtendedBinder.extBinder (Lean.binderIdent `i) []))
       ", "
       (Term.app `f' [`x (Term.app `Pi.single [`i (num "1")]) `i]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `f' [`x (Term.app `Pi.single [`i (num "1")]) `i])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `i
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.app `Pi.single [`i (num "1")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'num', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'num', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (num "1")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `i
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `Pi.single
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023,
     term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.app `Pi.single [`i (num "1")])
     ")")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `x
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `f'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, term) <=? (none, [anonymous])
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
       (BigOperators.Algebra.BigOperators.Basic.finset.sum_univ
        "∑"
        (Std.ExtendedBinder.extBinders (Std.ExtendedBinder.extBinder (Lean.binderIdent `i) []))
        ", "
        (Term.app `f' [`x (Term.paren "(" (Term.app `Pi.single [`i (num "1")]) ")") `i]))))
     ")")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `gP
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `I
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (Term.explicitUniv `HasIntegral ".{" [(num "0") "," `u "," `u] "}")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `u
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `u
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (num "0")
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `HasIntegral
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023,
     term) <=? (some 1023, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.explicitBinder', expected 'ident'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.explicitBinder', expected 'Lean.Parser.Term.hole'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Std.ExtendedBinder.«term∀__,_»
       "∀"
       (Lean.binderIdent `x)
       («binderTerm∈_» "∈" («term_\_» (Term.proj `I "." `IccCat) "\\" `s))
       ","
       (Term.app `HasFderivWithinAt [`f (Term.app `f' [`x]) (Term.proj `I "." `IccCat) `x]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `HasFderivWithinAt [`f (Term.app `f' [`x]) (Term.proj `I "." `IccCat) `x])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `x
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.proj', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.proj', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.proj `I "." `IccCat)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `I
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.app `f' [`x])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `x
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `f'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023,
     term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren "(" (Term.app `f' [`x]) ")")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `f
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `HasFderivWithinAt
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_\_» (Term.proj `I "." `IccCat) "\\" `s)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `s
[PrettyPrinter.parenthesize] ...precedences are 71 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 70, term))
      (Term.proj `I "." `IccCat)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `I
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 71 >? 1024, (none, [anonymous]) <=? (some 70, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 70, (some 71, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.explicitBinder', expected 'ident'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.explicitBinder', expected 'Lean.Parser.Term.hole'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Std.ExtendedBinder.«term∀__,_»
       "∀"
       (Lean.binderIdent `x)
       («binderTerm∈_» "∈" `s)
       ","
       (Term.app `ContinuousWithinAt [`f (Term.proj `I "." `IccCat) `x]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `ContinuousWithinAt [`f (Term.proj `I "." `IccCat) `x])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `x
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.proj', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.proj', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.proj `I "." `IccCat)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `I
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `f
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `ContinuousWithinAt
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `s
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.explicitBinder', expected 'ident'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.explicitBinder', expected 'Lean.Parser.Term.hole'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.proj `s "." `Countable)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `s
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.explicitBinder', expected 'ident'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.explicitBinder', expected 'Lean.Parser.Term.hole'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `Set [(BoxIntegral.Analysis.BoxIntegral.DivergenceTheorem.«termℝⁿ⁺¹» "ℝⁿ⁺¹")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'BoxIntegral.Analysis.BoxIntegral.DivergenceTheorem.«termℝⁿ⁺¹»', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'BoxIntegral.Analysis.BoxIntegral.DivergenceTheorem.«termℝⁿ⁺¹»', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (BoxIntegral.Analysis.BoxIntegral.DivergenceTheorem.«termℝⁿ⁺¹» "ℝⁿ⁺¹")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'BoxIntegral.Analysis.BoxIntegral.DivergenceTheorem.«termℝⁿ⁺¹»', expected 'BoxIntegral.Analysis.BoxIntegral.DivergenceTheorem.termℝⁿ⁺¹._@.Analysis.BoxIntegral.DivergenceTheorem._hyg.52'
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
    Divergence theorem for a Henstock-Kurzweil style integral.
    
    If `f : ℝⁿ⁺¹ → Eⁿ⁺¹` is differentiable on a closed rectangular box `I` with derivative `f'`, then
    the divergence `∑ i, f' x (pi.single i 1) i` is Henstock-Kurzweil integrable with integral equal to
    the sum of integrals of `f` over the faces of `I` taken with appropriate signs.
    
    More precisely, we use a non-standard generalization of the Henstock-Kurzweil integral and
    we allow `f` to be non-differentiable (but still continuous) at a countable set of points. -/
  theorem
    hasIntegralGPDivergenceOfForallHasDerivWithinAt
    ( f : ℝⁿ⁺¹ → Eⁿ⁺¹ )
        ( f' : ℝⁿ⁺¹ → ℝⁿ⁺¹ →L[ ℝ ] Eⁿ⁺¹ )
        ( s : Set ℝⁿ⁺¹ )
        ( hs : s . Countable )
        ( Hs : ∀ x ∈ s , ContinuousWithinAt f I . IccCat x )
        ( Hd : ∀ x ∈ I . IccCat \ s , HasFderivWithinAt f f' x I . IccCat x )
      :
        HasIntegral .{ 0 , u , u }
          I
            gP
            fun x => ∑ i , f' x Pi.single i 1 i
            BoxAdditiveMap.volume
            ∑
              i
              ,
              integral .{ 0 , u , u }
                  I . face i gP fun x => f i . insertNth I . upper i x i BoxAdditiveMap.volume
                -
                integral .{ 0 , u , u }
                  I . face i gP fun x => f i . insertNth I . lower i x i BoxAdditiveMap.volume
    :=
      by
        refine' has_integral_sum fun i hi => _
          ;
          clear hi
          simp only [ has_fderiv_within_at_pi' , continuous_within_at_pi ] at Hd Hs
          convert has_integral_GP_pderiv I _ _ s hs fun x hx => Hs x hx i fun x hx => Hd x hx i i
#align
  box_integral.has_integral_GP_divergence_of_forall_has_deriv_within_at BoxIntegral.hasIntegralGPDivergenceOfForallHasDerivWithinAt

end BoxIntegral

