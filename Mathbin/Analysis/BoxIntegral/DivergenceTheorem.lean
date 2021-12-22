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
defined on a box in `ℝⁿ` (it corresponds to the value `⊥` of `box_integral.integration_params` in
the definition of `box_integral.has_integral`).

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


open_locale Classical BigOperators Nnreal Ennreal TopologicalSpace BoxIntegral

open continuous_linear_map (lsmul)

open Filter Set Finset Metric

noncomputable section

universe u

variable {E : Type u} [NormedGroup E] [NormedSpace ℝ E] {n : ℕ}

namespace BoxIntegral

local notation "ℝⁿ" => Finₓ n → ℝ

local notation "ℝⁿ⁺¹" => Finₓ (n+1) → ℝ

local notation "Eⁿ⁺¹" => Finₓ (n+1) → E

variable [CompleteSpace E] (I : box (Finₓ (n+1))) {i : Finₓ (n+1)}

open MeasureTheory

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
 (Command.declModifiers [(Command.docComment "/--" " Auxiliary lemma for the divergence theorem. -/")] [] [] [] [] [])
 (Command.theorem
  "theorem"
  (Command.declId `norm_volume_sub_integral_face_upper_sub_lower_smul_le [])
  (Command.declSig
   [(Term.implicitBinder
     "{"
     [`f]
     [":" (Term.arrow (BoxIntegral.Analysis.BoxIntegral.DivergenceTheorem.«termℝⁿ⁺¹» "ℝⁿ⁺¹") "→" `E)]
     "}")
    (Term.implicitBinder
     "{"
     [`f']
     [":"
      (Topology.Algebra.Module.«term_→L[_]_»
       (BoxIntegral.Analysis.BoxIntegral.DivergenceTheorem.«termℝⁿ⁺¹» "ℝⁿ⁺¹")
       " →L["
       (Data.Real.Basic.termℝ "ℝ")
       "] "
       `E)]
     "}")
    (Term.explicitBinder "(" [`hfc] [":" (Term.app `ContinuousOn [`f `I.Icc])] [] ")")
    (Term.implicitBinder "{" [`x] [":" (BoxIntegral.Analysis.BoxIntegral.DivergenceTheorem.«termℝⁿ⁺¹» "ℝⁿ⁺¹")] "}")
    (Term.explicitBinder "(" [`hxI] [":" (Init.Core.«term_∈_» `x " ∈ " `I.Icc)] [] ")")
    (Term.implicitBinder "{" [`a] [":" `E] "}")
    (Term.implicitBinder "{" [`ε] [":" (Data.Real.Basic.termℝ "ℝ")] "}")
    (Term.explicitBinder "(" [`h0] [":" («term_<_» (numLit "0") "<" `ε)] [] ")")
    (Term.explicitBinder
     "("
     [`hε]
     [":"
      (Term.forall
       "∀"
       []
       ","
       (Mathlib.ExtendedBinder.«term∀___,_»
        "∀"
        `y
        («binderTerm∈_» "∈" `I.Icc)
        ","
        (Term.forall
         "∀"
         []
         ","
         («term_≤_»
          (Analysis.Normed.Group.Basic.«term∥_∥»
           "∥"
           («term_-_» («term_-_» (Term.app `f [`y]) "-" `a) "-" (Term.app `f' [(«term_-_» `y "-" `x)]))
           "∥")
          "≤"
          (Finset.Data.Finset.Fold.«term_*_»
           `ε
           "*"
           (Analysis.Normed.Group.Basic.«term∥_∥» "∥" («term_-_» `y "-" `x) "∥"))))))]
     []
     ")")
    (Term.implicitBinder "{" [`c] [":" (Data.Real.Nnreal.«termℝ≥0» " ℝ≥0 ")] "}")
    (Term.explicitBinder "(" [`hc] [":" («term_≤_» `I.distortion "≤" `c)] [] ")")]
   (Term.typeSpec
    ":"
    («term_≤_»
     (Analysis.Normed.Group.Basic.«term∥_∥»
      "∥"
      («term_-_»
       (Algebra.Group.Defs.«term_•_»
        (Algebra.BigOperators.Basic.«term∏_,_»
         "∏"
         (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `j)] []))
         ", "
         («term_-_» (Term.app `I.upper [`j]) "-" (Term.app `I.lower [`j])))
        " • "
        (Term.app `f' [(Term.app `Pi.single [`i (numLit "1")])]))
       "-"
       («term_-_»
        (Term.app
         `integral
         [(Term.app `I.face [`i])
          (Order.BoundedOrder.«term⊥» "⊥")
          (Rel.Data.Rel.«term_∘_» `f " ∘ " (Term.app `i.insert_nth [(Term.app `I.upper [`i])]))
          `box_additive_map.volume])
        "-"
        (Term.app
         `integral
         [(Term.app `I.face [`i])
          (Order.BoundedOrder.«term⊥» "⊥")
          (Rel.Data.Rel.«term_∘_» `f " ∘ " (Term.app `i.insert_nth [(Term.app `I.lower [`i])]))
          `box_additive_map.volume])))
      "∥")
     "≤"
     (Finset.Data.Finset.Fold.«term_*_»
      (Finset.Data.Finset.Fold.«term_*_» (Finset.Data.Finset.Fold.«term_*_» (numLit "2") "*" `ε) "*" `c)
      "*"
      (Algebra.BigOperators.Basic.«term∏_,_»
       "∏"
       (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `j)] []))
       ", "
       («term_-_» (Term.app `I.upper [`j]) "-" (Term.app `I.lower [`j])))))))
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
           [`Hl []]
           [(Term.typeSpec
             ":"
             (Init.Core.«term_∈_»
              (Term.app `I.lower [`i])
              " ∈ "
              (Term.app `Icc [(Term.app `I.lower [`i]) (Term.app `I.upper [`i])])))]
           ":="
           (Term.app (Term.proj `Set.left_mem_Icc "." (fieldIdx "2")) [(Term.app `I.lower_le_upper [`i])]))))
        [])
       (group
        (Tactic.tacticHave_
         "have"
         (Term.haveDecl
          (Term.haveIdDecl
           [`Hu []]
           [(Term.typeSpec
             ":"
             (Init.Core.«term_∈_»
              (Term.app `I.upper [`i])
              " ∈ "
              (Term.app `Icc [(Term.app `I.lower [`i]) (Term.app `I.upper [`i])])))]
           ":="
           (Term.app (Term.proj `Set.right_mem_Icc "." (fieldIdx "2")) [(Term.app `I.lower_le_upper [`i])]))))
        [])
       (group
        (Tactic.have''
         "have"
         [`Hi []]
         [(Term.typeSpec
           ":"
           (Term.forall
            "∀"
            []
            ","
            (Mathlib.ExtendedBinder.«term∀___,_»
             "∀"
             `x
             («binderTerm∈_» "∈" (Term.app `Icc [(Term.app `I.lower [`i]) (Term.app `I.upper [`i])]))
             ","
             (Term.forall
              "∀"
              []
              ","
              (Term.app
               (Term.explicitUniv `integrable ".{" [(numLit "0") "," `u "," `u] "}")
               [(Term.app `I.face [`i])
                (Order.BoundedOrder.«term⊥» "⊥")
                (Rel.Data.Rel.«term_∘_» `f " ∘ " (Term.app `i.insert_nth [`x]))
                `box_additive_map.volume])))))])
        [])
       (group
        (Tactic.exact
         "exact"
         (Term.fun
          "fun"
          (Term.basicFun
           [(Term.simpleBinder [`x `hx] [])]
           "=>"
           (Term.app
            `integrable_of_continuous_on
            [(Term.hole "_") (Term.app `box.continuous_on_face_Icc [`hfc `hx]) `volume]))))
        [])
       (group
        (Tactic.tacticHave_
         "have"
         (Term.haveDecl
          (Term.haveIdDecl
           []
           [(Term.typeSpec
             ":"
             (Term.forall
              "∀"
              []
              ","
              (Mathlib.ExtendedBinder.«term∀___,_»
               "∀"
               `y
               («binderTerm∈_» "∈" (Term.proj (Term.app `I.face [`i]) "." `Icc))
               ","
               (Term.forall
                "∀"
                []
                ","
                («term_≤_»
                 (Analysis.Normed.Group.Basic.«term∥_∥»
                  "∥"
                  («term_-_»
                   (Term.app
                    `f'
                    [(Term.app `Pi.single [`i («term_-_» (Term.app `I.upper [`i]) "-" (Term.app `I.lower [`i]))])])
                   "-"
                   («term_-_»
                    (Term.app `f [(Term.app `i.insert_nth [(Term.app `I.upper [`i]) `y])])
                    "-"
                    (Term.app `f [(Term.app `i.insert_nth [(Term.app `I.lower [`i]) `y])])))
                  "∥")
                 "≤"
                 (Finset.Data.Finset.Fold.«term_*_»
                  (Finset.Data.Finset.Fold.«term_*_» (numLit "2") "*" `ε)
                  "*"
                  (Term.app `diam [`I.Icc])))))))]
           ":="
           (Term.byTactic
            "by"
            (Tactic.tacticSeq
             (Tactic.tacticSeq1Indented
              [(group (Tactic.intro "intro" [`y `hy]) [])
               (group
                (Tactic.set
                 "set"
                 `g
                 []
                 ":="
                 (Term.fun
                  "fun"
                  (Term.basicFun
                   [(Term.simpleBinder [`y] [])]
                   "=>"
                   («term_-_» («term_-_» (Term.app `f [`y]) "-" `a) "-" (Term.app `f' [(«term_-_» `y "-" `x)]))))
                 ["with" [] `hg])
                [])
               (group
                (Tactic.change
                 "change"
                 (Term.forall
                  "∀"
                  []
                  ","
                  (Mathlib.ExtendedBinder.«term∀___,_»
                   "∀"
                   `y
                   («binderTerm∈_» "∈" `I.Icc)
                   ","
                   (Term.forall
                    "∀"
                    []
                    ","
                    («term_≤_»
                     (Analysis.Normed.Group.Basic.«term∥_∥» "∥" (Term.app `g [`y]) "∥")
                     "≤"
                     (Finset.Data.Finset.Fold.«term_*_»
                      `ε
                      "*"
                      (Analysis.Normed.Group.Basic.«term∥_∥» "∥" («term_-_» `y "-" `x) "∥"))))))
                 [(Tactic.location "at" (Tactic.locationHyp [`hε] []))])
                [])
               (group (Tactic.clearValue "clear_value" [`g]) [])
               (group
                (Tactic.obtain
                 "obtain"
                 [(Tactic.rcasesPatMed [(Tactic.rcasesPat.one `rfl)])]
                 [":"
                  («term_=_»
                   `f
                   "="
                   (Term.fun
                    "fun"
                    (Term.basicFun
                     [(Term.simpleBinder [`y] [])]
                     "=>"
                     (Init.Logic.«term_+_»
                      (Init.Logic.«term_+_» `a "+" (Term.app `f' [(«term_-_» `y "-" `x)]))
                      "+"
                      (Term.app `g [`y])))))]
                 [])
                [])
               (group
                (Tactic.«tactic·._»
                 "·"
                 (Tactic.tacticSeq
                  (Tactic.tacticSeq1Indented
                   [(group (Tactic.simp "simp" [] [] ["[" [(Tactic.simpLemma [] [] `hg)] "]"] []) [])])))
                [])
               (group
                (Tactic.convertTo
                 "convert_to"
                 («term_≤_»
                  (Analysis.Normed.Group.Basic.«term∥_∥»
                   "∥"
                   («term_-_»
                    (Term.app `g [(Term.app `i.insert_nth [(Term.app `I.lower [`i]) `y])])
                    "-"
                    (Term.app `g [(Term.app `i.insert_nth [(Term.app `I.upper [`i]) `y])]))
                   "∥")
                  "≤"
                  (Term.hole "_"))
                 [])
                [])
               (group
                (Tactic.«tactic·._»
                 "·"
                 (Tactic.tacticSeq
                  (Tactic.tacticSeq1Indented
                   [(group (Tactic.congr "congr" [(numLit "1")] []) [])
                    (group
                     (Tactic.tacticHave_
                      "have"
                      (Term.haveDecl
                       (Term.haveIdDecl
                        []
                        []
                        ":="
                        (Term.app
                         `Finₓ.insert_nth_sub_same
                         [`i (Term.app `I.upper [`i]) (Term.app `I.lower [`i]) `y]))))
                     [])
                    (group
                     (Tactic.simp
                      "simp"
                      []
                      ["only"]
                      ["[" [(Tactic.simpLemma [] ["←"] `this) "," (Tactic.simpLemma [] [] `f'.map_sub)] "]"]
                      [])
                     [])
                    (group (Tactic.abel "abel" [] []) [])])))
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
                        (Term.forall
                         "∀"
                         []
                         ","
                         (Mathlib.ExtendedBinder.«term∀___,_»
                          "∀"
                          `z
                          («binderTerm∈_» "∈" (Term.app `Icc [(Term.app `I.lower [`i]) (Term.app `I.upper [`i])]))
                          ","
                          (Term.forall
                           "∀"
                           []
                           ","
                           (Init.Core.«term_∈_» (Term.app `i.insert_nth [`z `y]) " ∈ " `I.Icc)))))])
                     [])
                    (group
                     (Tactic.exact
                      "exact"
                      (Term.fun
                       "fun"
                       (Term.basicFun
                        [(Term.simpleBinder [`z `hz] [])]
                        "=>"
                        (Term.app `I.maps_to_insert_nth_face_Icc [`hz `hy]))))
                     [])
                    (group
                     (Tactic.replace'
                      "replace"
                      [`hε []]
                      [(Term.typeSpec
                        ":"
                        (Term.forall
                         "∀"
                         []
                         ","
                         (Mathlib.ExtendedBinder.«term∀___,_»
                          "∀"
                          `y
                          («binderTerm∈_» "∈" `I.Icc)
                          ","
                          (Term.forall
                           "∀"
                           []
                           ","
                           («term_≤_»
                            (Analysis.Normed.Group.Basic.«term∥_∥» "∥" (Term.app `g [`y]) "∥")
                            "≤"
                            (Finset.Data.Finset.Fold.«term_*_» `ε "*" (Term.app `diam [`I.Icc])))))))])
                     [])
                    (group
                     (Tactic.«tactic·._»
                      "·"
                      (Tactic.tacticSeq
                       (Tactic.tacticSeq1Indented
                        [(group (Tactic.intro "intro" [`y `hy]) [])
                         (group
                          (Tactic.refine'
                           "refine'"
                           (Term.app
                            (Term.proj (Term.app `hε [`y `hy]) "." `trans)
                            [(Term.app `mul_le_mul_of_nonneg_left [(Term.hole "_") `h0.le])]))
                          [])
                         (group
                          (Tactic.rwSeq "rw" [] (Tactic.rwRuleSeq "[" [(Tactic.rwRule ["←"] `dist_eq_norm)] "]") [])
                          [])
                         (group
                          (Tactic.exact "exact" (Term.app `dist_le_diam_of_mem [`I.is_compact_Icc.bounded `hy `hxI]))
                          [])])))
                     [])
                    (group
                     (Tactic.rwSeq
                      "rw"
                      []
                      (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `two_mul) "," (Tactic.rwRule [] `add_mulₓ)] "]")
                      [])
                     [])
                    (group
                     (Tactic.exact
                      "exact"
                      (Term.app
                       `norm_sub_le_of_le
                       [(Term.app `hε [(Term.hole "_") (Term.app `this [(Term.hole "_") `Hl])])
                        (Term.app `hε [(Term.hole "_") (Term.app `this [(Term.hole "_") `Hu])])]))
                     [])])))
                [])]))))))
        [])
       (group
        (tacticCalc_
         "calc"
         [(calcStep
           («term_=_»
            (Analysis.Normed.Group.Basic.«term∥_∥»
             "∥"
             («term_-_»
              (Algebra.Group.Defs.«term_•_»
               (Algebra.BigOperators.Basic.«term∏_,_»
                "∏"
                (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `j)] []))
                ", "
                («term_-_» (Term.app `I.upper [`j]) "-" (Term.app `I.lower [`j])))
               " • "
               (Term.app `f' [(Term.app `Pi.single [`i (numLit "1")])]))
              "-"
              («term_-_»
               (Term.app
                `integral
                [(Term.app `I.face [`i])
                 (Order.BoundedOrder.«term⊥» "⊥")
                 (Rel.Data.Rel.«term_∘_» `f " ∘ " (Term.app `i.insert_nth [(Term.app `I.upper [`i])]))
                 `box_additive_map.volume])
               "-"
               (Term.app
                `integral
                [(Term.app `I.face [`i])
                 (Order.BoundedOrder.«term⊥» "⊥")
                 (Rel.Data.Rel.«term_∘_» `f " ∘ " (Term.app `i.insert_nth [(Term.app `I.lower [`i])]))
                 `box_additive_map.volume])))
             "∥")
            "="
            (Analysis.Normed.Group.Basic.«term∥_∥»
             "∥"
             (Term.app
              (Term.explicitUniv `integral ".{" [(numLit "0") "," `u "," `u] "}")
              [(Term.app `I.face [`i])
               (Order.BoundedOrder.«term⊥» "⊥")
               (Term.fun
                "fun"
                (Term.basicFun
                 [(Term.simpleBinder
                   [`x]
                   [(Term.typeSpec ":" (Term.arrow (Term.app `Finₓ [`n]) "→" (Data.Real.Basic.termℝ "ℝ")))])]
                 "=>"
                 («term_-_»
                  (Term.app
                   `f'
                   [(Term.app `Pi.single [`i («term_-_» (Term.app `I.upper [`i]) "-" (Term.app `I.lower [`i]))])])
                  "-"
                  («term_-_»
                   (Term.app `f [(Term.app `i.insert_nth [(Term.app `I.upper [`i]) `x])])
                   "-"
                   (Term.app `f [(Term.app `i.insert_nth [(Term.app `I.lower [`i]) `x])])))))
               `box_additive_map.volume])
             "∥"))
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
                    ["←"]
                    (Term.app
                     `integral_sub
                     [(Term.app `Hi [(Term.hole "_") `Hu]) (Term.app `Hi [(Term.hole "_") `Hl])]))
                   ","
                   (Tactic.rwRule ["←"] (Term.app `box.volume_face_mul [`i]))
                   ","
                   (Tactic.rwRule [] `mul_smul)
                   ","
                   (Tactic.rwRule ["←"] `box.volume_apply)
                   ","
                   (Tactic.rwRule ["←"] `box_additive_map.to_smul_apply)
                   ","
                   (Tactic.rwRule ["←"] `integral_const)
                   ","
                   (Tactic.rwRule ["←"] `box_additive_map.volume)
                   ","
                   (Tactic.rwRule
                    ["←"]
                    (Term.app
                     `integral_sub
                     [(Term.app `integrable_const [(Term.hole "_")])
                      (Term.app
                       (Term.proj (Term.app `Hi [(Term.hole "_") `Hu]) "." `sub)
                       [(Term.app `Hi [(Term.hole "_") `Hl])])]))]
                  "]")
                 [])
                [])
               (group
                (Tactic.simp
                 "simp"
                 []
                 ["only"]
                 ["["
                  [(Tactic.simpLemma [] [] (Rel.Data.Rel.«term_∘_» (Term.cdot "·") " ∘ " (Term.cdot "·")))
                   ","
                   (Tactic.simpLemma [] [] `Pi.sub_def)
                   ","
                   (Tactic.simpLemma [] ["←"] `f'.map_smul)
                   ","
                   (Tactic.simpLemma [] ["←"] `Pi.single_smul')
                   ","
                   (Tactic.simpLemma [] [] `smul_eq_mul)
                   ","
                   (Tactic.simpLemma [] [] `mul_oneₓ)]
                  "]"]
                 [])
                [])]))))
          (calcStep
           («term_≤_»
            (Term.hole "_")
            "≤"
            (Finset.Data.Finset.Fold.«term_*_»
             (Term.proj
              (Term.app
               `volume
               [(Term.paren
                 "("
                 [(Term.app `I.face [`i])
                  [(Term.typeAscription
                    ":"
                    (Term.app `Set [(BoxIntegral.Analysis.BoxIntegral.DivergenceTheorem.«termℝⁿ» "ℝⁿ")]))]]
                 ")")])
              "."
              `toReal)
             "*"
             (Finset.Data.Finset.Fold.«term_*_»
              (Finset.Data.Finset.Fold.«term_*_» (Finset.Data.Finset.Fold.«term_*_» (numLit "2") "*" `ε) "*" `c)
              "*"
              («term_-_» (Term.app `I.upper [`i]) "-" (Term.app `I.lower [`i])))))
           ":="
           (Term.byTactic
            "by"
            (Tactic.tacticSeq
             (Tactic.tacticSeq1Indented
              [(group
                (Tactic.refine'
                 "refine'"
                 (Term.app
                  `norm_integral_le_of_le_const
                  [(Term.fun
                    "fun"
                    (Term.basicFun
                     [(Term.simpleBinder [`y `hy] [])]
                     "=>"
                     (Term.app (Term.proj (Term.app `this [`y `hy]) "." `trans) [(Term.hole "_")])))
                   `volume]))
                [])
               (group
                (Tactic.rwSeq
                 "rw"
                 []
                 (Tactic.rwRuleSeq
                  "["
                  [(Tactic.rwRule [] (Term.app `mul_assocₓ [(Finset.Data.Finset.Fold.«term_*_» (numLit "2") "*" `ε)]))]
                  "]")
                 [])
                [])
               (group
                (Tactic.exact
                 "exact"
                 (Term.app
                  `mul_le_mul_of_nonneg_left
                  [(Term.app `I.diam_Icc_le_of_distortion_le [`i `hc]) (Term.app `mul_nonneg [`zero_le_two `h0.le])]))
                [])]))))
          (calcStep
           («term_=_»
            (Term.hole "_")
            "="
            (Finset.Data.Finset.Fold.«term_*_»
             (Finset.Data.Finset.Fold.«term_*_» (Finset.Data.Finset.Fold.«term_*_» (numLit "2") "*" `ε) "*" `c)
             "*"
             (Algebra.BigOperators.Basic.«term∏_,_»
              "∏"
              (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `j)] []))
              ", "
              («term_-_» (Term.app `I.upper [`j]) "-" (Term.app `I.lower [`j])))))
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
                  [(Tactic.rwRule ["←"] `measure.to_box_additive_apply)
                   ","
                   (Tactic.rwRule [] `box.volume_apply)
                   ","
                   (Tactic.rwRule ["←"] (Term.app `I.volume_face_mul [`i]))]
                  "]")
                 [])
                [])
               (group (Tactic.acRfl "ac_rfl") [])]))))])
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
          [`Hl []]
          [(Term.typeSpec
            ":"
            (Init.Core.«term_∈_»
             (Term.app `I.lower [`i])
             " ∈ "
             (Term.app `Icc [(Term.app `I.lower [`i]) (Term.app `I.upper [`i])])))]
          ":="
          (Term.app (Term.proj `Set.left_mem_Icc "." (fieldIdx "2")) [(Term.app `I.lower_le_upper [`i])]))))
       [])
      (group
       (Tactic.tacticHave_
        "have"
        (Term.haveDecl
         (Term.haveIdDecl
          [`Hu []]
          [(Term.typeSpec
            ":"
            (Init.Core.«term_∈_»
             (Term.app `I.upper [`i])
             " ∈ "
             (Term.app `Icc [(Term.app `I.lower [`i]) (Term.app `I.upper [`i])])))]
          ":="
          (Term.app (Term.proj `Set.right_mem_Icc "." (fieldIdx "2")) [(Term.app `I.lower_le_upper [`i])]))))
       [])
      (group
       (Tactic.have''
        "have"
        [`Hi []]
        [(Term.typeSpec
          ":"
          (Term.forall
           "∀"
           []
           ","
           (Mathlib.ExtendedBinder.«term∀___,_»
            "∀"
            `x
            («binderTerm∈_» "∈" (Term.app `Icc [(Term.app `I.lower [`i]) (Term.app `I.upper [`i])]))
            ","
            (Term.forall
             "∀"
             []
             ","
             (Term.app
              (Term.explicitUniv `integrable ".{" [(numLit "0") "," `u "," `u] "}")
              [(Term.app `I.face [`i])
               (Order.BoundedOrder.«term⊥» "⊥")
               (Rel.Data.Rel.«term_∘_» `f " ∘ " (Term.app `i.insert_nth [`x]))
               `box_additive_map.volume])))))])
       [])
      (group
       (Tactic.exact
        "exact"
        (Term.fun
         "fun"
         (Term.basicFun
          [(Term.simpleBinder [`x `hx] [])]
          "=>"
          (Term.app
           `integrable_of_continuous_on
           [(Term.hole "_") (Term.app `box.continuous_on_face_Icc [`hfc `hx]) `volume]))))
       [])
      (group
       (Tactic.tacticHave_
        "have"
        (Term.haveDecl
         (Term.haveIdDecl
          []
          [(Term.typeSpec
            ":"
            (Term.forall
             "∀"
             []
             ","
             (Mathlib.ExtendedBinder.«term∀___,_»
              "∀"
              `y
              («binderTerm∈_» "∈" (Term.proj (Term.app `I.face [`i]) "." `Icc))
              ","
              (Term.forall
               "∀"
               []
               ","
               («term_≤_»
                (Analysis.Normed.Group.Basic.«term∥_∥»
                 "∥"
                 («term_-_»
                  (Term.app
                   `f'
                   [(Term.app `Pi.single [`i («term_-_» (Term.app `I.upper [`i]) "-" (Term.app `I.lower [`i]))])])
                  "-"
                  («term_-_»
                   (Term.app `f [(Term.app `i.insert_nth [(Term.app `I.upper [`i]) `y])])
                   "-"
                   (Term.app `f [(Term.app `i.insert_nth [(Term.app `I.lower [`i]) `y])])))
                 "∥")
                "≤"
                (Finset.Data.Finset.Fold.«term_*_»
                 (Finset.Data.Finset.Fold.«term_*_» (numLit "2") "*" `ε)
                 "*"
                 (Term.app `diam [`I.Icc])))))))]
          ":="
          (Term.byTactic
           "by"
           (Tactic.tacticSeq
            (Tactic.tacticSeq1Indented
             [(group (Tactic.intro "intro" [`y `hy]) [])
              (group
               (Tactic.set
                "set"
                `g
                []
                ":="
                (Term.fun
                 "fun"
                 (Term.basicFun
                  [(Term.simpleBinder [`y] [])]
                  "=>"
                  («term_-_» («term_-_» (Term.app `f [`y]) "-" `a) "-" (Term.app `f' [(«term_-_» `y "-" `x)]))))
                ["with" [] `hg])
               [])
              (group
               (Tactic.change
                "change"
                (Term.forall
                 "∀"
                 []
                 ","
                 (Mathlib.ExtendedBinder.«term∀___,_»
                  "∀"
                  `y
                  («binderTerm∈_» "∈" `I.Icc)
                  ","
                  (Term.forall
                   "∀"
                   []
                   ","
                   («term_≤_»
                    (Analysis.Normed.Group.Basic.«term∥_∥» "∥" (Term.app `g [`y]) "∥")
                    "≤"
                    (Finset.Data.Finset.Fold.«term_*_»
                     `ε
                     "*"
                     (Analysis.Normed.Group.Basic.«term∥_∥» "∥" («term_-_» `y "-" `x) "∥"))))))
                [(Tactic.location "at" (Tactic.locationHyp [`hε] []))])
               [])
              (group (Tactic.clearValue "clear_value" [`g]) [])
              (group
               (Tactic.obtain
                "obtain"
                [(Tactic.rcasesPatMed [(Tactic.rcasesPat.one `rfl)])]
                [":"
                 («term_=_»
                  `f
                  "="
                  (Term.fun
                   "fun"
                   (Term.basicFun
                    [(Term.simpleBinder [`y] [])]
                    "=>"
                    (Init.Logic.«term_+_»
                     (Init.Logic.«term_+_» `a "+" (Term.app `f' [(«term_-_» `y "-" `x)]))
                     "+"
                     (Term.app `g [`y])))))]
                [])
               [])
              (group
               (Tactic.«tactic·._»
                "·"
                (Tactic.tacticSeq
                 (Tactic.tacticSeq1Indented
                  [(group (Tactic.simp "simp" [] [] ["[" [(Tactic.simpLemma [] [] `hg)] "]"] []) [])])))
               [])
              (group
               (Tactic.convertTo
                "convert_to"
                («term_≤_»
                 (Analysis.Normed.Group.Basic.«term∥_∥»
                  "∥"
                  («term_-_»
                   (Term.app `g [(Term.app `i.insert_nth [(Term.app `I.lower [`i]) `y])])
                   "-"
                   (Term.app `g [(Term.app `i.insert_nth [(Term.app `I.upper [`i]) `y])]))
                  "∥")
                 "≤"
                 (Term.hole "_"))
                [])
               [])
              (group
               (Tactic.«tactic·._»
                "·"
                (Tactic.tacticSeq
                 (Tactic.tacticSeq1Indented
                  [(group (Tactic.congr "congr" [(numLit "1")] []) [])
                   (group
                    (Tactic.tacticHave_
                     "have"
                     (Term.haveDecl
                      (Term.haveIdDecl
                       []
                       []
                       ":="
                       (Term.app `Finₓ.insert_nth_sub_same [`i (Term.app `I.upper [`i]) (Term.app `I.lower [`i]) `y]))))
                    [])
                   (group
                    (Tactic.simp
                     "simp"
                     []
                     ["only"]
                     ["[" [(Tactic.simpLemma [] ["←"] `this) "," (Tactic.simpLemma [] [] `f'.map_sub)] "]"]
                     [])
                    [])
                   (group (Tactic.abel "abel" [] []) [])])))
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
                       (Term.forall
                        "∀"
                        []
                        ","
                        (Mathlib.ExtendedBinder.«term∀___,_»
                         "∀"
                         `z
                         («binderTerm∈_» "∈" (Term.app `Icc [(Term.app `I.lower [`i]) (Term.app `I.upper [`i])]))
                         ","
                         (Term.forall
                          "∀"
                          []
                          ","
                          (Init.Core.«term_∈_» (Term.app `i.insert_nth [`z `y]) " ∈ " `I.Icc)))))])
                    [])
                   (group
                    (Tactic.exact
                     "exact"
                     (Term.fun
                      "fun"
                      (Term.basicFun
                       [(Term.simpleBinder [`z `hz] [])]
                       "=>"
                       (Term.app `I.maps_to_insert_nth_face_Icc [`hz `hy]))))
                    [])
                   (group
                    (Tactic.replace'
                     "replace"
                     [`hε []]
                     [(Term.typeSpec
                       ":"
                       (Term.forall
                        "∀"
                        []
                        ","
                        (Mathlib.ExtendedBinder.«term∀___,_»
                         "∀"
                         `y
                         («binderTerm∈_» "∈" `I.Icc)
                         ","
                         (Term.forall
                          "∀"
                          []
                          ","
                          («term_≤_»
                           (Analysis.Normed.Group.Basic.«term∥_∥» "∥" (Term.app `g [`y]) "∥")
                           "≤"
                           (Finset.Data.Finset.Fold.«term_*_» `ε "*" (Term.app `diam [`I.Icc])))))))])
                    [])
                   (group
                    (Tactic.«tactic·._»
                     "·"
                     (Tactic.tacticSeq
                      (Tactic.tacticSeq1Indented
                       [(group (Tactic.intro "intro" [`y `hy]) [])
                        (group
                         (Tactic.refine'
                          "refine'"
                          (Term.app
                           (Term.proj (Term.app `hε [`y `hy]) "." `trans)
                           [(Term.app `mul_le_mul_of_nonneg_left [(Term.hole "_") `h0.le])]))
                         [])
                        (group
                         (Tactic.rwSeq "rw" [] (Tactic.rwRuleSeq "[" [(Tactic.rwRule ["←"] `dist_eq_norm)] "]") [])
                         [])
                        (group
                         (Tactic.exact "exact" (Term.app `dist_le_diam_of_mem [`I.is_compact_Icc.bounded `hy `hxI]))
                         [])])))
                    [])
                   (group
                    (Tactic.rwSeq
                     "rw"
                     []
                     (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `two_mul) "," (Tactic.rwRule [] `add_mulₓ)] "]")
                     [])
                    [])
                   (group
                    (Tactic.exact
                     "exact"
                     (Term.app
                      `norm_sub_le_of_le
                      [(Term.app `hε [(Term.hole "_") (Term.app `this [(Term.hole "_") `Hl])])
                       (Term.app `hε [(Term.hole "_") (Term.app `this [(Term.hole "_") `Hu])])]))
                    [])])))
               [])]))))))
       [])
      (group
       (tacticCalc_
        "calc"
        [(calcStep
          («term_=_»
           (Analysis.Normed.Group.Basic.«term∥_∥»
            "∥"
            («term_-_»
             (Algebra.Group.Defs.«term_•_»
              (Algebra.BigOperators.Basic.«term∏_,_»
               "∏"
               (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `j)] []))
               ", "
               («term_-_» (Term.app `I.upper [`j]) "-" (Term.app `I.lower [`j])))
              " • "
              (Term.app `f' [(Term.app `Pi.single [`i (numLit "1")])]))
             "-"
             («term_-_»
              (Term.app
               `integral
               [(Term.app `I.face [`i])
                (Order.BoundedOrder.«term⊥» "⊥")
                (Rel.Data.Rel.«term_∘_» `f " ∘ " (Term.app `i.insert_nth [(Term.app `I.upper [`i])]))
                `box_additive_map.volume])
              "-"
              (Term.app
               `integral
               [(Term.app `I.face [`i])
                (Order.BoundedOrder.«term⊥» "⊥")
                (Rel.Data.Rel.«term_∘_» `f " ∘ " (Term.app `i.insert_nth [(Term.app `I.lower [`i])]))
                `box_additive_map.volume])))
            "∥")
           "="
           (Analysis.Normed.Group.Basic.«term∥_∥»
            "∥"
            (Term.app
             (Term.explicitUniv `integral ".{" [(numLit "0") "," `u "," `u] "}")
             [(Term.app `I.face [`i])
              (Order.BoundedOrder.«term⊥» "⊥")
              (Term.fun
               "fun"
               (Term.basicFun
                [(Term.simpleBinder
                  [`x]
                  [(Term.typeSpec ":" (Term.arrow (Term.app `Finₓ [`n]) "→" (Data.Real.Basic.termℝ "ℝ")))])]
                "=>"
                («term_-_»
                 (Term.app
                  `f'
                  [(Term.app `Pi.single [`i («term_-_» (Term.app `I.upper [`i]) "-" (Term.app `I.lower [`i]))])])
                 "-"
                 («term_-_»
                  (Term.app `f [(Term.app `i.insert_nth [(Term.app `I.upper [`i]) `x])])
                  "-"
                  (Term.app `f [(Term.app `i.insert_nth [(Term.app `I.lower [`i]) `x])])))))
              `box_additive_map.volume])
            "∥"))
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
                   ["←"]
                   (Term.app `integral_sub [(Term.app `Hi [(Term.hole "_") `Hu]) (Term.app `Hi [(Term.hole "_") `Hl])]))
                  ","
                  (Tactic.rwRule ["←"] (Term.app `box.volume_face_mul [`i]))
                  ","
                  (Tactic.rwRule [] `mul_smul)
                  ","
                  (Tactic.rwRule ["←"] `box.volume_apply)
                  ","
                  (Tactic.rwRule ["←"] `box_additive_map.to_smul_apply)
                  ","
                  (Tactic.rwRule ["←"] `integral_const)
                  ","
                  (Tactic.rwRule ["←"] `box_additive_map.volume)
                  ","
                  (Tactic.rwRule
                   ["←"]
                   (Term.app
                    `integral_sub
                    [(Term.app `integrable_const [(Term.hole "_")])
                     (Term.app
                      (Term.proj (Term.app `Hi [(Term.hole "_") `Hu]) "." `sub)
                      [(Term.app `Hi [(Term.hole "_") `Hl])])]))]
                 "]")
                [])
               [])
              (group
               (Tactic.simp
                "simp"
                []
                ["only"]
                ["["
                 [(Tactic.simpLemma [] [] (Rel.Data.Rel.«term_∘_» (Term.cdot "·") " ∘ " (Term.cdot "·")))
                  ","
                  (Tactic.simpLemma [] [] `Pi.sub_def)
                  ","
                  (Tactic.simpLemma [] ["←"] `f'.map_smul)
                  ","
                  (Tactic.simpLemma [] ["←"] `Pi.single_smul')
                  ","
                  (Tactic.simpLemma [] [] `smul_eq_mul)
                  ","
                  (Tactic.simpLemma [] [] `mul_oneₓ)]
                 "]"]
                [])
               [])]))))
         (calcStep
          («term_≤_»
           (Term.hole "_")
           "≤"
           (Finset.Data.Finset.Fold.«term_*_»
            (Term.proj
             (Term.app
              `volume
              [(Term.paren
                "("
                [(Term.app `I.face [`i])
                 [(Term.typeAscription
                   ":"
                   (Term.app `Set [(BoxIntegral.Analysis.BoxIntegral.DivergenceTheorem.«termℝⁿ» "ℝⁿ")]))]]
                ")")])
             "."
             `toReal)
            "*"
            (Finset.Data.Finset.Fold.«term_*_»
             (Finset.Data.Finset.Fold.«term_*_» (Finset.Data.Finset.Fold.«term_*_» (numLit "2") "*" `ε) "*" `c)
             "*"
             («term_-_» (Term.app `I.upper [`i]) "-" (Term.app `I.lower [`i])))))
          ":="
          (Term.byTactic
           "by"
           (Tactic.tacticSeq
            (Tactic.tacticSeq1Indented
             [(group
               (Tactic.refine'
                "refine'"
                (Term.app
                 `norm_integral_le_of_le_const
                 [(Term.fun
                   "fun"
                   (Term.basicFun
                    [(Term.simpleBinder [`y `hy] [])]
                    "=>"
                    (Term.app (Term.proj (Term.app `this [`y `hy]) "." `trans) [(Term.hole "_")])))
                  `volume]))
               [])
              (group
               (Tactic.rwSeq
                "rw"
                []
                (Tactic.rwRuleSeq
                 "["
                 [(Tactic.rwRule [] (Term.app `mul_assocₓ [(Finset.Data.Finset.Fold.«term_*_» (numLit "2") "*" `ε)]))]
                 "]")
                [])
               [])
              (group
               (Tactic.exact
                "exact"
                (Term.app
                 `mul_le_mul_of_nonneg_left
                 [(Term.app `I.diam_Icc_le_of_distortion_le [`i `hc]) (Term.app `mul_nonneg [`zero_le_two `h0.le])]))
               [])]))))
         (calcStep
          («term_=_»
           (Term.hole "_")
           "="
           (Finset.Data.Finset.Fold.«term_*_»
            (Finset.Data.Finset.Fold.«term_*_» (Finset.Data.Finset.Fold.«term_*_» (numLit "2") "*" `ε) "*" `c)
            "*"
            (Algebra.BigOperators.Basic.«term∏_,_»
             "∏"
             (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `j)] []))
             ", "
             («term_-_» (Term.app `I.upper [`j]) "-" (Term.app `I.lower [`j])))))
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
                 [(Tactic.rwRule ["←"] `measure.to_box_additive_apply)
                  ","
                  (Tactic.rwRule [] `box.volume_apply)
                  ","
                  (Tactic.rwRule ["←"] (Term.app `I.volume_face_mul [`i]))]
                 "]")
                [])
               [])
              (group (Tactic.acRfl "ac_rfl") [])]))))])
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
     («term_=_»
      (Analysis.Normed.Group.Basic.«term∥_∥»
       "∥"
       («term_-_»
        (Algebra.Group.Defs.«term_•_»
         (Algebra.BigOperators.Basic.«term∏_,_»
          "∏"
          (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `j)] []))
          ", "
          («term_-_» (Term.app `I.upper [`j]) "-" (Term.app `I.lower [`j])))
         " • "
         (Term.app `f' [(Term.app `Pi.single [`i (numLit "1")])]))
        "-"
        («term_-_»
         (Term.app
          `integral
          [(Term.app `I.face [`i])
           (Order.BoundedOrder.«term⊥» "⊥")
           (Rel.Data.Rel.«term_∘_» `f " ∘ " (Term.app `i.insert_nth [(Term.app `I.upper [`i])]))
           `box_additive_map.volume])
         "-"
         (Term.app
          `integral
          [(Term.app `I.face [`i])
           (Order.BoundedOrder.«term⊥» "⊥")
           (Rel.Data.Rel.«term_∘_» `f " ∘ " (Term.app `i.insert_nth [(Term.app `I.lower [`i])]))
           `box_additive_map.volume])))
       "∥")
      "="
      (Analysis.Normed.Group.Basic.«term∥_∥»
       "∥"
       (Term.app
        (Term.explicitUniv `integral ".{" [(numLit "0") "," `u "," `u] "}")
        [(Term.app `I.face [`i])
         (Order.BoundedOrder.«term⊥» "⊥")
         (Term.fun
          "fun"
          (Term.basicFun
           [(Term.simpleBinder
             [`x]
             [(Term.typeSpec ":" (Term.arrow (Term.app `Finₓ [`n]) "→" (Data.Real.Basic.termℝ "ℝ")))])]
           "=>"
           («term_-_»
            (Term.app
             `f'
             [(Term.app `Pi.single [`i («term_-_» (Term.app `I.upper [`i]) "-" (Term.app `I.lower [`i]))])])
            "-"
            («term_-_»
             (Term.app `f [(Term.app `i.insert_nth [(Term.app `I.upper [`i]) `x])])
             "-"
             (Term.app `f [(Term.app `i.insert_nth [(Term.app `I.lower [`i]) `x])])))))
         `box_additive_map.volume])
       "∥"))
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
              ["←"]
              (Term.app `integral_sub [(Term.app `Hi [(Term.hole "_") `Hu]) (Term.app `Hi [(Term.hole "_") `Hl])]))
             ","
             (Tactic.rwRule ["←"] (Term.app `box.volume_face_mul [`i]))
             ","
             (Tactic.rwRule [] `mul_smul)
             ","
             (Tactic.rwRule ["←"] `box.volume_apply)
             ","
             (Tactic.rwRule ["←"] `box_additive_map.to_smul_apply)
             ","
             (Tactic.rwRule ["←"] `integral_const)
             ","
             (Tactic.rwRule ["←"] `box_additive_map.volume)
             ","
             (Tactic.rwRule
              ["←"]
              (Term.app
               `integral_sub
               [(Term.app `integrable_const [(Term.hole "_")])
                (Term.app
                 (Term.proj (Term.app `Hi [(Term.hole "_") `Hu]) "." `sub)
                 [(Term.app `Hi [(Term.hole "_") `Hl])])]))]
            "]")
           [])
          [])
         (group
          (Tactic.simp
           "simp"
           []
           ["only"]
           ["["
            [(Tactic.simpLemma [] [] (Rel.Data.Rel.«term_∘_» (Term.cdot "·") " ∘ " (Term.cdot "·")))
             ","
             (Tactic.simpLemma [] [] `Pi.sub_def)
             ","
             (Tactic.simpLemma [] ["←"] `f'.map_smul)
             ","
             (Tactic.simpLemma [] ["←"] `Pi.single_smul')
             ","
             (Tactic.simpLemma [] [] `smul_eq_mul)
             ","
             (Tactic.simpLemma [] [] `mul_oneₓ)]
            "]"]
           [])
          [])]))))
    (calcStep
     («term_≤_»
      (Term.hole "_")
      "≤"
      (Finset.Data.Finset.Fold.«term_*_»
       (Term.proj
        (Term.app
         `volume
         [(Term.paren
           "("
           [(Term.app `I.face [`i])
            [(Term.typeAscription
              ":"
              (Term.app `Set [(BoxIntegral.Analysis.BoxIntegral.DivergenceTheorem.«termℝⁿ» "ℝⁿ")]))]]
           ")")])
        "."
        `toReal)
       "*"
       (Finset.Data.Finset.Fold.«term_*_»
        (Finset.Data.Finset.Fold.«term_*_» (Finset.Data.Finset.Fold.«term_*_» (numLit "2") "*" `ε) "*" `c)
        "*"
        («term_-_» (Term.app `I.upper [`i]) "-" (Term.app `I.lower [`i])))))
     ":="
     (Term.byTactic
      "by"
      (Tactic.tacticSeq
       (Tactic.tacticSeq1Indented
        [(group
          (Tactic.refine'
           "refine'"
           (Term.app
            `norm_integral_le_of_le_const
            [(Term.fun
              "fun"
              (Term.basicFun
               [(Term.simpleBinder [`y `hy] [])]
               "=>"
               (Term.app (Term.proj (Term.app `this [`y `hy]) "." `trans) [(Term.hole "_")])))
             `volume]))
          [])
         (group
          (Tactic.rwSeq
           "rw"
           []
           (Tactic.rwRuleSeq
            "["
            [(Tactic.rwRule [] (Term.app `mul_assocₓ [(Finset.Data.Finset.Fold.«term_*_» (numLit "2") "*" `ε)]))]
            "]")
           [])
          [])
         (group
          (Tactic.exact
           "exact"
           (Term.app
            `mul_le_mul_of_nonneg_left
            [(Term.app `I.diam_Icc_le_of_distortion_le [`i `hc]) (Term.app `mul_nonneg [`zero_le_two `h0.le])]))
          [])]))))
    (calcStep
     («term_=_»
      (Term.hole "_")
      "="
      (Finset.Data.Finset.Fold.«term_*_»
       (Finset.Data.Finset.Fold.«term_*_» (Finset.Data.Finset.Fold.«term_*_» (numLit "2") "*" `ε) "*" `c)
       "*"
       (Algebra.BigOperators.Basic.«term∏_,_»
        "∏"
        (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `j)] []))
        ", "
        («term_-_» (Term.app `I.upper [`j]) "-" (Term.app `I.lower [`j])))))
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
            [(Tactic.rwRule ["←"] `measure.to_box_additive_apply)
             ","
             (Tactic.rwRule [] `box.volume_apply)
             ","
             (Tactic.rwRule ["←"] (Term.app `I.volume_face_mul [`i]))]
            "]")
           [])
          [])
         (group (Tactic.acRfl "ac_rfl") [])]))))])
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
         [(Tactic.rwRule ["←"] `measure.to_box_additive_apply)
          ","
          (Tactic.rwRule [] `box.volume_apply)
          ","
          (Tactic.rwRule ["←"] (Term.app `I.volume_face_mul [`i]))]
         "]")
        [])
       [])
      (group (Tactic.acRfl "ac_rfl") [])])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.byTactic', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.byTactic', expected 'Lean.Parser.Term.byTactic.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq', expected 'Lean.Parser.Tactic.tacticSeq.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeq1Indented.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'group', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Tactic.acRfl "ac_rfl")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.acRfl', expected 'antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'group', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, tactic))
  (Tactic.rwSeq
   "rw"
   []
   (Tactic.rwRuleSeq
    "["
    [(Tactic.rwRule ["←"] `measure.to_box_additive_apply)
     ","
     (Tactic.rwRule [] `box.volume_apply)
     ","
     (Tactic.rwRule ["←"] (Term.app `I.volume_face_mul [`i]))]
    "]")
   [])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.rwSeq', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.rwRule', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.app `I.volume_face_mul [`i])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `i
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `I.volume_face_mul
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«←»', expected 'optional.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.rwRule', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `box.volume_apply
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.rwRule', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `measure.to_box_additive_apply
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«←»', expected 'optional.antiquot_scope'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, tactic) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  («term_=_»
   (Term.hole "_")
   "="
   (Finset.Data.Finset.Fold.«term_*_»
    (Finset.Data.Finset.Fold.«term_*_» (Finset.Data.Finset.Fold.«term_*_» (numLit "2") "*" `ε) "*" `c)
    "*"
    (Algebra.BigOperators.Basic.«term∏_,_»
     "∏"
     (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `j)] []))
     ", "
     («term_-_» (Term.app `I.upper [`j]) "-" (Term.app `I.lower [`j])))))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_=_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Finset.Data.Finset.Fold.«term_*_»
   (Finset.Data.Finset.Fold.«term_*_» (Finset.Data.Finset.Fold.«term_*_» (numLit "2") "*" `ε) "*" `c)
   "*"
   (Algebra.BigOperators.Basic.«term∏_,_»
    "∏"
    (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `j)] []))
    ", "
    («term_-_» (Term.app `I.upper [`j]) "-" (Term.app `I.lower [`j]))))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Finset.Data.Finset.Fold.«term_*_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Algebra.BigOperators.Basic.«term∏_,_»
   "∏"
   (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `j)] []))
   ", "
   («term_-_» (Term.app `I.upper [`j]) "-" (Term.app `I.lower [`j])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Algebra.BigOperators.Basic.«term∏_,_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  («term_-_» (Term.app `I.upper [`j]) "-" (Term.app `I.lower [`j]))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_-_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.app `I.lower [`j])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `j
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `I.lower
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 66 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 65, term))
  (Term.app `I.upper [`j])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `j
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `I.upper
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 65 >? 1022, (some 1023, term) <=? (some 65, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 65, (some 66, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.explicitBinders', expected 'Mathlib.ExtendedBinder.extBinders'
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
/-- Auxiliary lemma for the divergence theorem. -/
  theorem
    norm_volume_sub_integral_face_upper_sub_lower_smul_le
    { f : ℝⁿ⁺¹ → E }
        { f' : ℝⁿ⁺¹ →L[ ℝ ] E }
        ( hfc : ContinuousOn f I.Icc )
        { x : ℝⁿ⁺¹ }
        ( hxI : x ∈ I.Icc )
        { a : E }
        { ε : ℝ }
        ( h0 : 0 < ε )
        ( hε : ∀ , ∀ y ∈ I.Icc , ∀ , ∥ f y - a - f' y - x ∥ ≤ ε * ∥ y - x ∥ )
        { c : ℝ≥0 }
        ( hc : I.distortion ≤ c )
      :
        ∥
            ∏ j , I.upper j - I.lower j • f' Pi.single i 1
              -
              integral I.face i ⊥ f ∘ i.insert_nth I.upper i box_additive_map.volume
                -
                integral I.face i ⊥ f ∘ i.insert_nth I.lower i box_additive_map.volume
            ∥
          ≤
          2 * ε * c * ∏ j , I.upper j - I.lower j
    :=
      by
        have Hl : I.lower i ∈ Icc I.lower i I.upper i := Set.left_mem_Icc . 2 I.lower_le_upper i
          have Hu : I.upper i ∈ Icc I.lower i I.upper i := Set.right_mem_Icc . 2 I.lower_le_upper i
          have
            Hi
            :
              ∀
                ,
                ∀
                  x
                  ∈ Icc I.lower i I.upper i
                  ,
                  ∀ , integrable .{ 0 , u , u } I.face i ⊥ f ∘ i.insert_nth x box_additive_map.volume
          exact fun x hx => integrable_of_continuous_on _ box.continuous_on_face_Icc hfc hx volume
          have
            :
                ∀
                  ,
                  ∀
                    y
                    ∈ I.face i . Icc
                    ,
                    ∀
                      ,
                      ∥ f' Pi.single i I.upper i - I.lower i - f i.insert_nth I.upper i y - f i.insert_nth I.lower i y ∥
                        ≤
                        2 * ε * diam I.Icc
              :=
              by
                intro y hy
                  set g := fun y => f y - a - f' y - x with hg
                  change ∀ , ∀ y ∈ I.Icc , ∀ , ∥ g y ∥ ≤ ε * ∥ y - x ∥ at hε
                  clear_value g
                  obtain rfl : f = fun y => a + f' y - x + g y
                  · simp [ hg ]
                  convert_to ∥ g i.insert_nth I.lower i y - g i.insert_nth I.upper i y ∥ ≤ _
                  ·
                    congr 1
                      have := Finₓ.insert_nth_sub_same i I.upper i I.lower i y
                      simp only [ ← this , f'.map_sub ]
                      abel
                  ·
                    have : ∀ , ∀ z ∈ Icc I.lower i I.upper i , ∀ , i.insert_nth z y ∈ I.Icc
                      exact fun z hz => I.maps_to_insert_nth_face_Icc hz hy
                      replace hε : ∀ , ∀ y ∈ I.Icc , ∀ , ∥ g y ∥ ≤ ε * diam I.Icc
                      ·
                        intro y hy
                          refine' hε y hy . trans mul_le_mul_of_nonneg_left _ h0.le
                          rw [ ← dist_eq_norm ]
                          exact dist_le_diam_of_mem I.is_compact_Icc.bounded hy hxI
                      rw [ two_mul , add_mulₓ ]
                      exact norm_sub_le_of_le hε _ this _ Hl hε _ this _ Hu
          calc
            ∥
                    ∏ j , I.upper j - I.lower j • f' Pi.single i 1
                      -
                      integral I.face i ⊥ f ∘ i.insert_nth I.upper i box_additive_map.volume
                        -
                        integral I.face i ⊥ f ∘ i.insert_nth I.lower i box_additive_map.volume
                    ∥
                  =
                  ∥
                    integral .{ 0 , u , u }
                      I.face i
                        ⊥
                        fun
                          x : Finₓ n → ℝ
                            =>
                            f' Pi.single i I.upper i - I.lower i
                              -
                              f i.insert_nth I.upper i x - f i.insert_nth I.lower i x
                        box_additive_map.volume
                    ∥
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
                    simp only [ · ∘ · , Pi.sub_def , ← f'.map_smul , ← Pi.single_smul' , smul_eq_mul , mul_oneₓ ]
              _ ≤ volume ( I.face i : Set ℝⁿ ) . toReal * 2 * ε * c * I.upper i - I.lower i
                :=
                by
                  refine' norm_integral_le_of_le_const fun y hy => this y hy . trans _ volume
                    rw [ mul_assocₓ 2 * ε ]
                    exact mul_le_mul_of_nonneg_left I.diam_Icc_le_of_distortion_le i hc mul_nonneg zero_le_two h0.le
              _ = 2 * ε * c * ∏ j , I.upper j - I.lower j
                :=
                by rw [ ← measure.to_box_additive_apply , box.volume_apply , ← I.volume_face_mul i ] ac_rfl

-- ././Mathport/Syntax/Translate/Basic.lean:477:2: warning: expanding binder collection (y₁ y₂ «expr ∈ » «expr ∩ »(closed_ball x δ, I.Icc))
/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
 (Command.declModifiers
  [(Command.docComment
    "/--"
    " If `f : ℝⁿ⁺¹ → E` is differentiable on a closed rectangular box `I` with derivative `f'`, then\nthe partial derivative `λ x, f' x (pi.single i 1)` is Henstock-Kurzweil integrable with integral\nequal to the difference of integrals of `f` over the faces `x i = I.upper i` and `x i = I.lower i`.\n\nMore precisely, we use a non-standard generalization of the Henstock-Kurzweil integral and\nwe allow `f` to be non-differentiable (but still continuous) at a countable set of points.\n\nTODO: If `n > 0`, then the condition at `x ∈ s` can be replaced by a much weaker estimate but this\nrequires either better integrability theorems, or usage of a filter depending on the countable set\n`s` (we need to ensure that none of the faces of a partition contain a point from `s`). -/")]
  []
  []
  []
  []
  [])
 (Command.theorem
  "theorem"
  (Command.declId `has_integral_bot_pderiv [])
  (Command.declSig
   [(Term.explicitBinder
     "("
     [`f]
     [":" (Term.arrow (BoxIntegral.Analysis.BoxIntegral.DivergenceTheorem.«termℝⁿ⁺¹» "ℝⁿ⁺¹") "→" `E)]
     []
     ")")
    (Term.explicitBinder
     "("
     [`f']
     [":"
      (Term.arrow
       (BoxIntegral.Analysis.BoxIntegral.DivergenceTheorem.«termℝⁿ⁺¹» "ℝⁿ⁺¹")
       "→"
       (Topology.Algebra.Module.«term_→L[_]_»
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
     [":" (Term.app `Set [(BoxIntegral.Analysis.BoxIntegral.DivergenceTheorem.«termℝⁿ⁺¹» "ℝⁿ⁺¹")])]
     []
     ")")
    (Term.explicitBinder "(" [`hs] [":" (Term.app `countable [`s])] [] ")")
    (Term.explicitBinder
     "("
     [`Hs]
     [":"
      (Term.forall
       "∀"
       []
       ","
       (Mathlib.ExtendedBinder.«term∀___,_»
        "∀"
        `x
        («binderTerm∈_» "∈" `s)
        ","
        (Term.forall "∀" [] "," (Term.app `ContinuousWithinAt [`f `I.Icc `x]))))]
     []
     ")")
    (Term.explicitBinder
     "("
     [`Hd]
     [":"
      (Term.forall
       "∀"
       []
       ","
       (Mathlib.ExtendedBinder.«term∀___,_»
        "∀"
        `x
        («binderTerm∈_» "∈" (Init.Core.«term_\_» `I.Icc " \\ " `s))
        ","
        (Term.forall "∀" [] "," (Term.app `HasFderivWithinAt [`f (Term.app `f' [`x]) `I.Icc `x]))))]
     []
     ")")
    (Term.explicitBinder "(" [`i] [":" (Term.app `Finₓ [(Init.Logic.«term_+_» `n "+" (numLit "1"))])] [] ")")]
   (Term.typeSpec
    ":"
    (Term.app
     (Term.explicitUniv `has_integral ".{" [(numLit "0") "," `u "," `u] "}")
     [`I
      (Order.BoundedOrder.«term⊥» "⊥")
      (Term.fun
       "fun"
       (Term.basicFun [(Term.simpleBinder [`x] [])] "=>" (Term.app `f' [`x (Term.app `Pi.single [`i (numLit "1")])])))
      `box_additive_map.volume
      («term_-_»
       (Term.app
        (Term.explicitUniv `integral ".{" [(numLit "0") "," `u "," `u] "}")
        [(Term.app `I.face [`i])
         (Order.BoundedOrder.«term⊥» "⊥")
         (Term.fun
          "fun"
          (Term.basicFun
           [(Term.simpleBinder [`x] [])]
           "=>"
           (Term.app `f [(Term.app `i.insert_nth [(Term.app `I.upper [`i]) `x])])))
         `box_additive_map.volume])
       "-"
       (Term.app
        (Term.explicitUniv `integral ".{" [(numLit "0") "," `u "," `u] "}")
        [(Term.app `I.face [`i])
         (Order.BoundedOrder.«term⊥» "⊥")
         (Term.fun
          "fun"
          (Term.basicFun
           [(Term.simpleBinder [`x] [])]
           "=>"
           (Term.app `f [(Term.app `i.insert_nth [(Term.app `I.lower [`i]) `x])])))
         `box_additive_map.volume]))])))
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
           [`Hc []]
           [(Term.typeSpec ":" (Term.app `ContinuousOn [`f `I.Icc]))]
           ":="
           (Term.byTactic
            "by"
            (Tactic.tacticSeq
             (Tactic.tacticSeq1Indented
              [(group (Tactic.intro "intro" [`x `hx]) [])
               (group (Tactic.byCases' "by_cases'" [`hxs ":"] (Init.Core.«term_∈_» `x " ∈ " `s)) [])
               (group
                (exacts
                 "exacts"
                 "["
                 [(Term.app `Hs [`x `hxs])
                  ","
                  (Term.proj (Term.app `Hd [`x (Term.anonymousCtor "⟨" [`hx "," `hxs] "⟩")]) "." `ContinuousWithinAt)]
                 "]")
                [])]))))))
        [])
       (group
        (Tactic.set
         "set"
         `fI
         [":" (Term.arrow (Data.Real.Basic.termℝ "ℝ") "→" (Term.arrow (Term.app `box [(Term.app `Finₓ [`n])]) "→" `E))]
         ":="
         (Term.fun
          "fun"
          (Term.basicFun
           [(Term.simpleBinder [`y `J] [])]
           "=>"
           (Term.app
            (Term.explicitUniv `integral ".{" [(numLit "0") "," `u "," `u] "}")
            [`J
             (Order.BoundedOrder.«term⊥» "⊥")
             (Term.fun
              "fun"
              (Term.basicFun [(Term.simpleBinder [`x] [])] "=>" (Term.app `f [(Term.app `i.insert_nth [`y `x])])))
             `box_additive_map.volume])))
         [])
        [])
       (group
        (Tactic.set
         "set"
         `fb
         [":"
          (Term.arrow
           (Term.app `Icc [(Term.app `I.lower [`i]) (Term.app `I.upper [`i])])
           "→"
           (BoxIntegral.Analysis.BoxIntegral.Partition.Additive.«term_→ᵇᵃ[_]_»
            (Term.app `Finₓ [`n])
            " →ᵇᵃ["
            (Init.Coe.«term↑_» "↑" (Term.app `I.face [`i]))
            "] "
            `E))]
         ":="
         (Term.fun
          "fun"
          (Term.basicFun
           [(Term.simpleBinder [`x] [])]
           "=>"
           (Term.proj
            (Term.app
             `integrable_of_continuous_on
             [(Order.BoundedOrder.«term⊥» "⊥")
              (Term.app `box.continuous_on_face_Icc [`Hc (Term.proj `x "." (fieldIdx "2"))])
              `volume])
            "."
            `toBoxAdditive)))
         [])
        [])
       (group
        (Tactic.set
         "set"
         `F
         [":"
          (BoxIntegral.Analysis.BoxIntegral.Partition.Additive.«term_→ᵇᵃ[_]_»
           (Term.app `Finₓ [(Init.Logic.«term_+_» `n "+" (numLit "1"))])
           " →ᵇᵃ["
           `I
           "] "
           `E)]
         ":="
         (Term.app
          `box_additive_map.upper_sub_lower
          [`I `i `fI `fb (Term.fun "fun" (Term.basicFun [(Term.simpleBinder [`x `hx `J] [])] "=>" `rfl))])
         [])
        [])
       (group
        (Tactic.change
         "change"
         (Term.app
          `has_integral
          [`I
           (Order.BoundedOrder.«term⊥» "⊥")
           (Term.fun
            "fun"
            (Term.basicFun
             [(Term.simpleBinder [`x] [])]
             "=>"
             (Term.app `f' [`x (Term.app `Pi.single [`i (numLit "1")])])))
           (Term.hole "_")
           (Term.app `F [`I])])
         [])
        [])
       (group
        (Tactic.refine'
         "refine'"
         (Term.app
          `has_integral_of_le_Henstock_of_forall_is_o
          [`bot_le (Term.hole "_") (Term.hole "_") (Term.hole "_") `s `hs (Term.hole "_") (Term.hole "_")]))
        [])
       (group
        (Tactic.«tactic·._»
         "·"
         (Tactic.tacticSeq
          (Tactic.tacticSeq1Indented
           [(group
             (Tactic.exact
              "exact"
              (Term.app
               (Term.proj
                (Term.proj
                 (Term.paren
                  "("
                  [`volume
                   [(Term.typeAscription
                     ":"
                     (Term.app `Measureₓ [(BoxIntegral.Analysis.BoxIntegral.DivergenceTheorem.«termℝⁿ⁺¹» "ℝⁿ⁺¹")]))]]
                  ")")
                 "."
                 `toBoxAdditive)
                "."
                `restrict)
               [(Term.hole "_") `le_top]))
             [])])))
        [])
       (group
        (Tactic.«tactic·._»
         "·"
         (Tactic.tacticSeq
          (Tactic.tacticSeq1Indented
           [(group
             (Tactic.exact
              "exact"
              (Term.fun "fun" (Term.basicFun [(Term.simpleBinder [`J] [])] "=>" `Ennreal.to_real_nonneg)))
             [])])))
        [])
       (group
        (Tactic.«tactic·._»
         "·"
         (Tactic.tacticSeq
          (Tactic.tacticSeq1Indented
           [(group (Tactic.intro "intro" [`c `x `hx `ε `ε0]) [])
            (group
             (Tactic.tacticHave_
              "have"
              (Term.haveDecl
               (Term.haveIdDecl
                []
                [(Term.typeSpec
                  ":"
                  (Filter.Order.Filter.Basic.«term∀ᶠ_in_,_»
                   "∀ᶠ"
                   (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `δ)] []))
                   " in "
                   (Topology.Basic.«term𝓝[>]_»
                    "𝓝[>] "
                    (Term.paren "(" [(numLit "0") [(Term.typeAscription ":" (Data.Real.Basic.termℝ "ℝ"))]] ")"))
                   ", "
                   («term_∧_»
                    (Init.Core.«term_∈_»
                     `δ
                     " ∈ "
                     (Term.app
                      `Ioc
                      [(Term.paren "(" [(numLit "0") [(Term.typeAscription ":" (Data.Real.Basic.termℝ "ℝ"))]] ")")
                       («term_/_» (numLit "1") "/" (numLit "2"))]))
                    "∧"
                    («term_∧_»
                     (Term.forall
                      "∀"
                      [(Term.simpleBinder [`y₁ `y₂] [])
                       (Term.simpleBinder
                        [(Term.hole "_")]
                        [(Term.typeSpec
                          ":"
                          (Init.Core.«term_∈_»
                           `y₁
                           " ∈ "
                           (Init.Core.«term_∩_» (Term.app `closed_ball [`x `δ]) " ∩ " `I.Icc)))])
                       (Term.simpleBinder
                        [(Term.hole "_")]
                        [(Term.typeSpec
                          ":"
                          (Init.Core.«term_∈_»
                           `y₂
                           " ∈ "
                           (Init.Core.«term_∩_» (Term.app `closed_ball [`x `δ]) " ∩ " `I.Icc)))])]
                      ","
                      («term_≤_»
                       (Analysis.Normed.Group.Basic.«term∥_∥»
                        "∥"
                        («term_-_» (Term.app `f [`y₁]) "-" (Term.app `f [`y₂]))
                        "∥")
                       "≤"
                       («term_/_» `ε "/" (numLit "2"))))
                     "∧"
                     («term_≤_»
                      (Finset.Data.Finset.Fold.«term_*_»
                       (Cardinal.SetTheory.Cofinality.«term_^_»
                        (Finset.Data.Finset.Fold.«term_*_» (numLit "2") "*" `δ)
                        "^"
                        (Init.Logic.«term_+_» `n "+" (numLit "1")))
                       "*"
                       (Analysis.Normed.Group.Basic.«term∥_∥»
                        "∥"
                        (Term.app `f' [`x (Term.app `Pi.single [`i (numLit "1")])])
                        "∥"))
                      "≤"
                      («term_/_» `ε "/" (numLit "2")))))))]
                ":="
                (Term.byTactic
                 "by"
                 (Tactic.tacticSeq
                  (Tactic.tacticSeq1Indented
                   [(group
                     (Tactic.refine'
                      "refine'"
                      (Term.app
                       `eventually.and
                       [(Term.hole "_") (Term.app `eventually.and [(Term.hole "_") (Term.hole "_")])]))
                     [])
                    (group
                     (Tactic.«tactic·._»
                      "·"
                      (Tactic.tacticSeq
                       (Tactic.tacticSeq1Indented
                        [(group
                          (Tactic.exact
                           "exact"
                           (Term.app
                            `Ioc_mem_nhds_within_Ioi
                            [(Term.anonymousCtor "⟨" [`le_rfl "," `one_half_pos] "⟩")]))
                          [])])))
                     [])
                    (group
                     (Tactic.«tactic·._»
                      "·"
                      (Tactic.tacticSeq
                       (Tactic.tacticSeq1Indented
                        [(group
                          (Tactic.rcases
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
                               («term_$__» `half_pos "$" (Term.app `half_pos [`ε0]))]))]
                           ["with"
                            (Tactic.rcasesPat.tuple
                             "⟨"
                             [(Tactic.rcasesPatLo (Tactic.rcasesPatMed [(Tactic.rcasesPat.one `δ₁)]) [])
                              ","
                              (Tactic.rcasesPatLo (Tactic.rcasesPatMed [(Tactic.rcasesPat.one `δ₁0)]) [])
                              ","
                              (Tactic.rcasesPatLo (Tactic.rcasesPatMed [(Tactic.rcasesPat.one `hδ₁)]) [])]
                             "⟩")])
                          [])
                         (group
                          (Tactic.filterUpwards
                           "filter_upwards"
                           "["
                           [(Term.app `Ioc_mem_nhds_within_Ioi [(Term.anonymousCtor "⟨" [`le_rfl "," `δ₁0] "⟩")])]
                           "]"
                           [])
                          [])
                         (group
                          (Tactic.rintro
                           "rintro"
                           [(Tactic.rintroPat.one (Tactic.rcasesPat.one `δ))
                            (Tactic.rintroPat.one (Tactic.rcasesPat.one `hδ))
                            (Tactic.rintroPat.one (Tactic.rcasesPat.one `y₁))
                            (Tactic.rintroPat.one (Tactic.rcasesPat.one `y₂))
                            (Tactic.rintroPat.one (Tactic.rcasesPat.one `hy₁))
                            (Tactic.rintroPat.one (Tactic.rcasesPat.one `hy₂))]
                           [])
                          [])
                         (group
                          (Tactic.have''
                           "have"
                           []
                           [(Term.typeSpec
                             ":"
                             (Init.Core.«term_⊆_»
                              (Init.Core.«term_∩_» (Term.app `closed_ball [`x `δ]) " ∩ " `I.Icc)
                              " ⊆ "
                              (Init.Core.«term_∩_» (Term.app `closed_ball [`x `δ₁]) " ∩ " `I.Icc)))])
                          [])
                         (group
                          (Tactic.exact
                           "exact"
                           (Term.app
                            `inter_subset_inter_left
                            [(Term.hole "_")
                             (Term.app `closed_ball_subset_closed_ball [(Term.proj `hδ "." (fieldIdx "2"))])]))
                          [])
                         (group
                          (Tactic.rwSeq "rw" [] (Tactic.rwRuleSeq "[" [(Tactic.rwRule ["←"] `dist_eq_norm)] "]") [])
                          [])
                         (group
                          (tacticCalc_
                           "calc"
                           [(calcStep
                             («term_≤_»
                              (Term.app `dist [(Term.app `f [`y₁]) (Term.app `f [`y₂])])
                              "≤"
                              (Init.Logic.«term_+_»
                               (Term.app `dist [(Term.app `f [`y₁]) (Term.app `f [`x])])
                               "+"
                               (Term.app `dist [(Term.app `f [`y₂]) (Term.app `f [`x])])))
                             ":="
                             (Term.app `dist_triangle_right [(Term.hole "_") (Term.hole "_") (Term.hole "_")]))
                            (calcStep
                             («term_≤_»
                              (Term.hole "_")
                              "≤"
                              (Init.Logic.«term_+_»
                               («term_/_» («term_/_» `ε "/" (numLit "2")) "/" (numLit "2"))
                               "+"
                               («term_/_» («term_/_» `ε "/" (numLit "2")) "/" (numLit "2"))))
                             ":="
                             (Term.app
                              `add_le_add
                              [(«term_$__» (Term.app `hδ₁ [(Term.hole "_")]) "$" (Term.app `this [`hy₁]))
                               («term_$__» (Term.app `hδ₁ [(Term.hole "_")]) "$" (Term.app `this [`hy₂]))]))
                            (calcStep
                             («term_=_» (Term.hole "_") "=" («term_/_» `ε "/" (numLit "2")))
                             ":="
                             (Term.app `add_halves [(Term.hole "_")]))])
                          [])])))
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
                             [(Term.typeSpec
                               ":"
                               (Term.app
                                `ContinuousWithinAt
                                [(Term.fun
                                  "fun"
                                  (Term.basicFun
                                   [(Term.simpleBinder [`δ] [])]
                                   "=>"
                                   (Finset.Data.Finset.Fold.«term_*_»
                                    (Cardinal.SetTheory.Cofinality.«term_^_»
                                     (Finset.Data.Finset.Fold.«term_*_» (numLit "2") "*" `δ)
                                     "^"
                                     (Init.Logic.«term_+_» `n "+" (numLit "1")))
                                    "*"
                                    (Analysis.Normed.Group.Basic.«term∥_∥»
                                     "∥"
                                     (Term.app `f' [`x (Term.app `Pi.single [`i (numLit "1")])])
                                     "∥"))))
                                 (Term.app
                                  `Ioi
                                  [(Term.paren
                                    "("
                                    [(numLit "0") [(Term.typeAscription ":" (Data.Real.Basic.termℝ "ℝ"))]]
                                    ")")])
                                 (numLit "0")]))]
                             ":="
                             (Term.app
                              (Term.proj
                               (Term.app
                                (Term.proj (Term.app `continuous_within_at_id.const_mul [(Term.hole "_")]) "." `pow)
                                [(Term.hole "_")])
                               "."
                               `mul_const)
                              [(Term.hole "_")]))))
                          [])
                         (group
                          (Tactic.refine'
                           "refine'"
                           (Term.app `this.eventually [(Term.app `ge_mem_nhds [(Term.hole "_")])]))
                          [])
                         (group (Tactic.simpa "simpa" [] [] [] [] ["using" (Term.app `half_pos [`ε0])]) [])])))
                     [])]))))))
             [])
            (group
             (Tactic.rcases
              "rcases"
              [(Tactic.casesTarget [] `this.exists)]
              ["with"
               (Tactic.rcasesPat.tuple
                "⟨"
                [(Tactic.rcasesPatLo (Tactic.rcasesPatMed [(Tactic.rcasesPat.one `δ)]) [])
                 ","
                 (Tactic.rcasesPatLo
                  (Tactic.rcasesPatMed
                   [(Tactic.rcasesPat.tuple
                     "⟨"
                     [(Tactic.rcasesPatLo (Tactic.rcasesPatMed [(Tactic.rcasesPat.one `hδ0)]) [])
                      ","
                      (Tactic.rcasesPatLo (Tactic.rcasesPatMed [(Tactic.rcasesPat.one `hδ12)]) [])]
                     "⟩")])
                  [])
                 ","
                 (Tactic.rcasesPatLo (Tactic.rcasesPatMed [(Tactic.rcasesPat.one `hdfδ)]) [])
                 ","
                 (Tactic.rcasesPatLo (Tactic.rcasesPatMed [(Tactic.rcasesPat.one `hδ)]) [])]
                "⟩")])
             [])
            (group
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
                  [(Term.simpleBinder [`J `hJI `hJδ `hxJ `hJc] [])]
                  "=>"
                  (Term.subst (Term.app `add_halves [`ε]) "▸" [(Term.hole "_")])))]
               "⟩"))
             [])
            (group
             (Tactic.tacticHave_
              "have"
              (Term.haveDecl
               (Term.haveIdDecl
                [`Hl []]
                [(Term.typeSpec
                  ":"
                  (Init.Core.«term_∈_»
                   (Term.app `J.lower [`i])
                   " ∈ "
                   (Term.app `Icc [(Term.app `J.lower [`i]) (Term.app `J.upper [`i])])))]
                ":="
                (Term.app (Term.proj `Set.left_mem_Icc "." (fieldIdx "2")) [(Term.app `J.lower_le_upper [`i])]))))
             [])
            (group
             (Tactic.tacticHave_
              "have"
              (Term.haveDecl
               (Term.haveIdDecl
                [`Hu []]
                [(Term.typeSpec
                  ":"
                  (Init.Core.«term_∈_»
                   (Term.app `J.upper [`i])
                   " ∈ "
                   (Term.app `Icc [(Term.app `J.lower [`i]) (Term.app `J.upper [`i])])))]
                ":="
                (Term.app (Term.proj `Set.right_mem_Icc "." (fieldIdx "2")) [(Term.app `J.lower_le_upper [`i])]))))
             [])
            (group
             (Tactic.have''
              "have"
              [`Hi []]
              [(Term.typeSpec
                ":"
                (Term.forall
                 "∀"
                 []
                 ","
                 (Mathlib.ExtendedBinder.«term∀___,_»
                  "∀"
                  `x
                  («binderTerm∈_» "∈" (Term.app `Icc [(Term.app `J.lower [`i]) (Term.app `J.upper [`i])]))
                  ","
                  (Term.forall
                   "∀"
                   []
                   ","
                   (Term.app
                    (Term.explicitUniv `integrable ".{" [(numLit "0") "," `u "," `u] "}")
                    [(Term.app `J.face [`i])
                     (Order.BoundedOrder.«term⊥» "⊥")
                     (Term.fun
                      "fun"
                      (Term.basicFun
                       [(Term.simpleBinder [`y] [])]
                       "=>"
                       (Term.app `f [(Term.app `i.insert_nth [`x `y])])))
                     `box_additive_map.volume])))))])
             [])
            (group
             (Tactic.exact
              "exact"
              (Term.fun
               "fun"
               (Term.basicFun
                [(Term.simpleBinder [`x `hx] [])]
                "=>"
                (Term.app
                 `integrable_of_continuous_on
                 [(Term.hole "_")
                  (Term.app
                   `box.continuous_on_face_Icc
                   [(«term_$__» `Hc.mono "$" (Term.app (Term.proj `box.le_iff_Icc "." (fieldIdx "1")) [`hJI])) `hx])
                  `volume]))))
             [])
            (group
             (Tactic.have''
              "have"
              [`hJδ' []]
              [(Term.typeSpec
                ":"
                (Init.Core.«term_⊆_» `J.Icc " ⊆ " (Init.Core.«term_∩_» (Term.app `closed_ball [`x `δ]) " ∩ " `I.Icc)))])
             [])
            (group
             (Tactic.exact
              "exact"
              (Term.app `subset_inter [`hJδ (Term.app (Term.proj `box.le_iff_Icc "." (fieldIdx "1")) [`hJI])]))
             [])
            (group
             (Tactic.have''
              "have"
              [`Hmaps []]
              [(Term.typeSpec
                ":"
                (Term.forall
                 "∀"
                 []
                 ","
                 (Mathlib.ExtendedBinder.«term∀___,_»
                  "∀"
                  `z
                  («binderTerm∈_» "∈" (Term.app `Icc [(Term.app `J.lower [`i]) (Term.app `J.upper [`i])]))
                  ","
                  (Term.forall
                   "∀"
                   []
                   ","
                   (Term.app
                    `maps_to
                    [(Term.app `i.insert_nth [`z])
                     (Term.proj (Term.app `J.face [`i]) "." `Icc)
                     (Init.Core.«term_∩_» (Term.app `closed_ball [`x `δ]) " ∩ " `I.Icc)])))))])
             [])
            (group
             (Tactic.exact
              "exact"
              (Term.fun
               "fun"
               (Term.basicFun
                [(Term.simpleBinder [`z `hz] [])]
                "=>"
                (Term.app (Term.proj (Term.app `J.maps_to_insert_nth_face_Icc [`hz]) "." `mono) [`subset.rfl `hJδ']))))
             [])
            (group
             (Tactic.simp
              "simp"
              []
              ["only"]
              ["["
               [(Tactic.simpLemma [] [] `dist_eq_norm) "," (Tactic.simpLemma [] [] `F) "," (Tactic.simpLemma [] [] `fI)]
               "]"]
              [])
             [])
            (group (Tactic.dsimp "dsimp" [] [] [] [] []) [])
            (group
             (Tactic.rwSeq
              "rw"
              []
              (Tactic.rwRuleSeq
               "["
               [(Tactic.rwRule
                 ["←"]
                 (Term.app `integral_sub [(Term.app `Hi [(Term.hole "_") `Hu]) (Term.app `Hi [(Term.hole "_") `Hl])]))]
               "]")
              [])
             [])
            (group
             (Tactic.refine'
              "refine'"
              (Term.app
               (Term.proj (Term.app `norm_sub_le [(Term.hole "_") (Term.hole "_")]) "." `trans)
               [(Term.app `add_le_add [(Term.hole "_") (Term.hole "_")])]))
             [])
            (group
             (Tactic.«tactic·._»
              "·"
              (Tactic.tacticSeq
               (Tactic.tacticSeq1Indented
                [(group
                  (Tactic.simpRw
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
                  [])
                 (group
                  (Tactic.refine'
                   "refine'"
                   (Term.app
                    (Term.proj
                     («term_$__»
                      (Term.app `mul_le_mul_of_nonneg_right [(Term.hole "_")])
                      "$"
                      (Term.app `norm_nonneg [(Term.hole "_")]))
                     "."
                     `trans)
                    [`hδ]))
                  [])
                 (group
                  (Tactic.tacticHave_
                   "have"
                   (Term.haveDecl
                    (Term.haveIdDecl
                     []
                     [(Term.typeSpec
                       ":"
                       (Term.forall
                        "∀"
                        [(Term.simpleBinder [`j] [])]
                        ","
                        («term_≤_»
                         (Analysis.NormedSpace.LatticeOrderedGroup.«term|_|»
                          "|"
                          («term_-_» (Term.app `J.upper [`j]) "-" (Term.app `J.lower [`j]))
                          "|")
                         "≤"
                         (Finset.Data.Finset.Fold.«term_*_» (numLit "2") "*" `δ))))]
                     ":="
                     (Term.byTactic
                      "by"
                      (Tactic.tacticSeq
                       (Tactic.tacticSeq1Indented
                        [(group (Tactic.intro "intro" [`j]) [])
                         (group
                          (tacticCalc_
                           "calc"
                           [(calcStep
                             («term_≤_»
                              (Term.app `dist [(Term.app `J.upper [`j]) (Term.app `J.lower [`j])])
                              "≤"
                              (Term.app `dist [`J.upper `J.lower]))
                             ":="
                             (Term.app `dist_le_pi_dist [(Term.hole "_") (Term.hole "_") (Term.hole "_")]))
                            (calcStep
                             («term_≤_»
                              (Term.hole "_")
                              "≤"
                              (Init.Logic.«term_+_» (Term.app `dist [`J.upper `x]) "+" (Term.app `dist [`J.lower `x])))
                             ":="
                             (Term.app `dist_triangle_right [(Term.hole "_") (Term.hole "_") (Term.hole "_")]))
                            (calcStep
                             («term_≤_» (Term.hole "_") "≤" (Init.Logic.«term_+_» `δ "+" `δ))
                             ":="
                             (Term.app
                              `add_le_add
                              [(Term.app `hJδ [`J.upper_mem_Icc]) (Term.app `hJδ [`J.lower_mem_Icc])]))
                            (calcStep
                             («term_=_» (Term.hole "_") "=" (Finset.Data.Finset.Fold.«term_*_» (numLit "2") "*" `δ))
                             ":="
                             (Term.proj (Term.app `two_mul [`δ]) "." `symm))])
                          [])]))))))
                  [])
                 (group
                  (tacticCalc_
                   "calc"
                   [(calcStep
                     («term_≤_»
                      (Algebra.BigOperators.Basic.«term∏_,_»
                       "∏"
                       (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `j)] []))
                       ", "
                       (Analysis.NormedSpace.LatticeOrderedGroup.«term|_|»
                        "|"
                        («term_-_» (Term.app `J.upper [`j]) "-" (Term.app `J.lower [`j]))
                        "|"))
                      "≤"
                      (Algebra.BigOperators.Basic.«term∏_,_»
                       "∏"
                       (Lean.explicitBinders
                        (Lean.unbracketedExplicitBinders
                         [(Lean.binderIdent `j)]
                         [":" (Term.app `Finₓ [(Init.Logic.«term_+_» `n "+" (numLit "1"))])]))
                       ", "
                       (Finset.Data.Finset.Fold.«term_*_» (numLit "2") "*" `δ)))
                     ":="
                     (Term.app
                      `prod_le_prod
                      [(Term.fun
                        "fun"
                        (Term.basicFun
                         [(Term.simpleBinder [(Term.hole "_") (Term.hole "_")] [])]
                         "=>"
                         (Term.app `abs_nonneg [(Term.hole "_")])))
                       (Term.fun "fun" (Term.basicFun [(Term.simpleBinder [`j `hj] [])] "=>" (Term.app `this [`j])))]))
                    (calcStep
                     («term_=_»
                      (Term.hole "_")
                      "="
                      (Cardinal.SetTheory.Cofinality.«term_^_»
                       (Finset.Data.Finset.Fold.«term_*_» (numLit "2") "*" `δ)
                       "^"
                       (Init.Logic.«term_+_» `n "+" (numLit "1"))))
                     ":="
                     (Term.byTactic
                      "by"
                      (Tactic.tacticSeq (Tactic.tacticSeq1Indented [(group (Tactic.simp "simp" [] [] [] []) [])]))))])
                  [])])))
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
                    (Term.proj
                     (Term.app
                      `norm_integral_le_of_le_const
                      [(Term.fun
                        "fun"
                        (Term.basicFun
                         [(Term.simpleBinder [`y `hy] [])]
                         "=>"
                         (Term.app
                          `hdfδ
                          [(Term.hole "_")
                           (Term.hole "_")
                           (Term.app `Hmaps [(Term.hole "_") `Hu `hy])
                           (Term.app `Hmaps [(Term.hole "_") `Hl `hy])])))
                       (Term.hole "_")])
                     "."
                     `trans)
                    [(Term.hole "_")]))
                  [])
                 (group
                  (Tactic.refine'
                   "refine'"
                   (Term.app
                    (Term.proj
                     (Term.app
                      `mul_le_mul_of_nonneg_right
                      [(Term.hole "_") (Term.proj (Term.app `half_pos [`ε0]) "." `le)])
                     "."
                     `trans_eq)
                    [(Term.app `one_mulₓ [(Term.hole "_")])]))
                  [])
                 (group
                  (Tactic.rwSeq
                   "rw"
                   []
                   (Tactic.rwRuleSeq
                    "["
                    [(Tactic.rwRule [] `box.coe_eq_pi)
                     ","
                     (Tactic.rwRule
                      []
                      (Term.app `Real.volume_pi_Ioc_to_real [(Term.app `box.lower_le_upper [(Term.hole "_")])]))]
                    "]")
                   [])
                  [])
                 (group
                  (Tactic.refine'
                   "refine'"
                   (Term.app
                    `prod_le_one
                    [(Term.fun
                      "fun"
                      (Term.basicFun
                       [(Term.simpleBinder [(Term.hole "_") (Term.hole "_")] [])]
                       "=>"
                       («term_$__»
                        (Term.proj `sub_nonneg "." (fieldIdx "2"))
                        "$"
                        (Term.app `box.lower_le_upper [(Term.hole "_") (Term.hole "_")]))))
                     (Term.fun "fun" (Term.basicFun [(Term.simpleBinder [`j `hj] [])] "=>" (Term.hole "_")))]))
                  [])
                 (group
                  (tacticCalc_
                   "calc"
                   [(calcStep
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
                    (calcStep
                     («term_≤_» (Term.hole "_") "≤" (Term.app `dist [`J.upper `J.lower]))
                     ":="
                     (Term.app `dist_le_pi_dist [`J.upper `J.lower (Term.app `i.succ_above [`j])]))
                    (calcStep
                     («term_≤_»
                      (Term.hole "_")
                      "≤"
                      (Init.Logic.«term_+_» (Term.app `dist [`J.upper `x]) "+" (Term.app `dist [`J.lower `x])))
                     ":="
                     (Term.app `dist_triangle_right [(Term.hole "_") (Term.hole "_") (Term.hole "_")]))
                    (calcStep
                     («term_≤_» (Term.hole "_") "≤" (Init.Logic.«term_+_» `δ "+" `δ))
                     ":="
                     (Term.app `add_le_add [(Term.app `hJδ [`J.upper_mem_Icc]) (Term.app `hJδ [`J.lower_mem_Icc])]))
                    (calcStep
                     («term_≤_»
                      (Term.hole "_")
                      "≤"
                      (Init.Logic.«term_+_»
                       («term_/_» (numLit "1") "/" (numLit "2"))
                       "+"
                       («term_/_» (numLit "1") "/" (numLit "2"))))
                     ":="
                     (Term.app `add_le_add [`hδ12 `hδ12]))
                    (calcStep («term_=_» (Term.hole "_") "=" (numLit "1")) ":=" (Term.app `add_halves [(numLit "1")]))])
                  [])])))
             [])])))
        [])
       (group
        (Tactic.«tactic·._»
         "·"
         (Tactic.tacticSeq
          (Tactic.tacticSeq1Indented
           [(group (Tactic.intro "intro" [`c `x `hx `ε `ε0]) [])
            (group
             (Tactic.rcases
              "rcases"
              [(Tactic.casesTarget
                []
                (Term.app `exists_pos_mul_lt [`ε0 (Finset.Data.Finset.Fold.«term_*_» (numLit "2") "*" `c)]))]
              ["with"
               (Tactic.rcasesPat.tuple
                "⟨"
                [(Tactic.rcasesPatLo (Tactic.rcasesPatMed [(Tactic.rcasesPat.one `ε')]) [])
                 ","
                 (Tactic.rcasesPatLo (Tactic.rcasesPatMed [(Tactic.rcasesPat.one `ε'0)]) [])
                 ","
                 (Tactic.rcasesPatLo (Tactic.rcasesPatMed [(Tactic.rcasesPat.one `hlt)]) [])]
                "⟩")])
             [])
            (group
             (Tactic.rcases
              "rcases"
              [(Tactic.casesTarget
                []
                (Term.app
                 (Term.proj
                  (Term.proj (Term.app `nhds_within_has_basis [`nhds_basis_closed_ball (Term.hole "_")]) "." `mem_iff)
                  "."
                  (fieldIdx "1"))
                 [(Term.app (Term.proj (Term.app `Hd [`x `hx]) "." `def) [`ε'0])]))]
              ["with"
               (Tactic.rcasesPat.tuple
                "⟨"
                [(Tactic.rcasesPatLo (Tactic.rcasesPatMed [(Tactic.rcasesPat.one `δ)]) [])
                 ","
                 (Tactic.rcasesPatLo (Tactic.rcasesPatMed [(Tactic.rcasesPat.one `δ0)]) [])
                 ","
                 (Tactic.rcasesPatLo (Tactic.rcasesPatMed [(Tactic.rcasesPat.one `Hδ)]) [])]
                "⟩")])
             [])
            (group
             (Tactic.refine'
              "refine'"
              (Term.anonymousCtor
               "⟨"
               [`δ
                ","
                `δ0
                ","
                (Term.fun "fun" (Term.basicFun [(Term.simpleBinder [`J `hle `hJδ `hxJ `hJc] [])] "=>" (Term.hole "_")))]
               "⟩"))
             [])
            (group
             (Tactic.simp
              "simp"
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
             [])
            (group
             (Tactic.refine'
              "refine'"
              (Term.app
               (Term.proj
                (Term.app
                 `norm_volume_sub_integral_face_upper_sub_lower_smul_le
                 [(Term.hole "_")
                  («term_$__» `Hc.mono "$" (Term.app (Term.proj `box.le_iff_Icc "." (fieldIdx "1")) [`hle]))
                  `hxJ
                  `ε'0
                  (Term.fun
                   "fun"
                   (Term.basicFun [(Term.simpleBinder [`y `hy] [])] "=>" (Term.app `Hδ [(Term.hole "_")])))
                  (Term.app `hJc [`rfl])])
                "."
                `trans)
               [(Term.hole "_")]))
             [])
            (group
             (Tactic.«tactic·._»
              "·"
              (Tactic.tacticSeq
               (Tactic.tacticSeq1Indented
                [(group
                  (Tactic.exact
                   "exact"
                   (Term.anonymousCtor
                    "⟨"
                    [(Term.app `hJδ [`hy]) "," (Term.app (Term.proj `box.le_iff_Icc "." (fieldIdx "1")) [`hle `hy])]
                    "⟩"))
                  [])])))
             [])
            (group
             (Tactic.«tactic·._»
              "·"
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
                       `mul_right_commₓ
                       [(Term.paren "(" [(numLit "2") [(Term.typeAscription ":" (Data.Real.Basic.termℝ "ℝ"))]] ")")]))
                     ","
                     (Tactic.rwRule ["←"] `box.volume_apply)]
                    "]")
                   [])
                  [])
                 (group
                  (Tactic.exact "exact" (Term.app `mul_le_mul_of_nonneg_right [`hlt.le `Ennreal.to_real_nonneg]))
                  [])])))
             [])])))
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
          [`Hc []]
          [(Term.typeSpec ":" (Term.app `ContinuousOn [`f `I.Icc]))]
          ":="
          (Term.byTactic
           "by"
           (Tactic.tacticSeq
            (Tactic.tacticSeq1Indented
             [(group (Tactic.intro "intro" [`x `hx]) [])
              (group (Tactic.byCases' "by_cases'" [`hxs ":"] (Init.Core.«term_∈_» `x " ∈ " `s)) [])
              (group
               (exacts
                "exacts"
                "["
                [(Term.app `Hs [`x `hxs])
                 ","
                 (Term.proj (Term.app `Hd [`x (Term.anonymousCtor "⟨" [`hx "," `hxs] "⟩")]) "." `ContinuousWithinAt)]
                "]")
               [])]))))))
       [])
      (group
       (Tactic.set
        "set"
        `fI
        [":" (Term.arrow (Data.Real.Basic.termℝ "ℝ") "→" (Term.arrow (Term.app `box [(Term.app `Finₓ [`n])]) "→" `E))]
        ":="
        (Term.fun
         "fun"
         (Term.basicFun
          [(Term.simpleBinder [`y `J] [])]
          "=>"
          (Term.app
           (Term.explicitUniv `integral ".{" [(numLit "0") "," `u "," `u] "}")
           [`J
            (Order.BoundedOrder.«term⊥» "⊥")
            (Term.fun
             "fun"
             (Term.basicFun [(Term.simpleBinder [`x] [])] "=>" (Term.app `f [(Term.app `i.insert_nth [`y `x])])))
            `box_additive_map.volume])))
        [])
       [])
      (group
       (Tactic.set
        "set"
        `fb
        [":"
         (Term.arrow
          (Term.app `Icc [(Term.app `I.lower [`i]) (Term.app `I.upper [`i])])
          "→"
          (BoxIntegral.Analysis.BoxIntegral.Partition.Additive.«term_→ᵇᵃ[_]_»
           (Term.app `Finₓ [`n])
           " →ᵇᵃ["
           (Init.Coe.«term↑_» "↑" (Term.app `I.face [`i]))
           "] "
           `E))]
        ":="
        (Term.fun
         "fun"
         (Term.basicFun
          [(Term.simpleBinder [`x] [])]
          "=>"
          (Term.proj
           (Term.app
            `integrable_of_continuous_on
            [(Order.BoundedOrder.«term⊥» "⊥")
             (Term.app `box.continuous_on_face_Icc [`Hc (Term.proj `x "." (fieldIdx "2"))])
             `volume])
           "."
           `toBoxAdditive)))
        [])
       [])
      (group
       (Tactic.set
        "set"
        `F
        [":"
         (BoxIntegral.Analysis.BoxIntegral.Partition.Additive.«term_→ᵇᵃ[_]_»
          (Term.app `Finₓ [(Init.Logic.«term_+_» `n "+" (numLit "1"))])
          " →ᵇᵃ["
          `I
          "] "
          `E)]
        ":="
        (Term.app
         `box_additive_map.upper_sub_lower
         [`I `i `fI `fb (Term.fun "fun" (Term.basicFun [(Term.simpleBinder [`x `hx `J] [])] "=>" `rfl))])
        [])
       [])
      (group
       (Tactic.change
        "change"
        (Term.app
         `has_integral
         [`I
          (Order.BoundedOrder.«term⊥» "⊥")
          (Term.fun
           "fun"
           (Term.basicFun
            [(Term.simpleBinder [`x] [])]
            "=>"
            (Term.app `f' [`x (Term.app `Pi.single [`i (numLit "1")])])))
          (Term.hole "_")
          (Term.app `F [`I])])
        [])
       [])
      (group
       (Tactic.refine'
        "refine'"
        (Term.app
         `has_integral_of_le_Henstock_of_forall_is_o
         [`bot_le (Term.hole "_") (Term.hole "_") (Term.hole "_") `s `hs (Term.hole "_") (Term.hole "_")]))
       [])
      (group
       (Tactic.«tactic·._»
        "·"
        (Tactic.tacticSeq
         (Tactic.tacticSeq1Indented
          [(group
            (Tactic.exact
             "exact"
             (Term.app
              (Term.proj
               (Term.proj
                (Term.paren
                 "("
                 [`volume
                  [(Term.typeAscription
                    ":"
                    (Term.app `Measureₓ [(BoxIntegral.Analysis.BoxIntegral.DivergenceTheorem.«termℝⁿ⁺¹» "ℝⁿ⁺¹")]))]]
                 ")")
                "."
                `toBoxAdditive)
               "."
               `restrict)
              [(Term.hole "_") `le_top]))
            [])])))
       [])
      (group
       (Tactic.«tactic·._»
        "·"
        (Tactic.tacticSeq
         (Tactic.tacticSeq1Indented
          [(group
            (Tactic.exact
             "exact"
             (Term.fun "fun" (Term.basicFun [(Term.simpleBinder [`J] [])] "=>" `Ennreal.to_real_nonneg)))
            [])])))
       [])
      (group
       (Tactic.«tactic·._»
        "·"
        (Tactic.tacticSeq
         (Tactic.tacticSeq1Indented
          [(group (Tactic.intro "intro" [`c `x `hx `ε `ε0]) [])
           (group
            (Tactic.tacticHave_
             "have"
             (Term.haveDecl
              (Term.haveIdDecl
               []
               [(Term.typeSpec
                 ":"
                 (Filter.Order.Filter.Basic.«term∀ᶠ_in_,_»
                  "∀ᶠ"
                  (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `δ)] []))
                  " in "
                  (Topology.Basic.«term𝓝[>]_»
                   "𝓝[>] "
                   (Term.paren "(" [(numLit "0") [(Term.typeAscription ":" (Data.Real.Basic.termℝ "ℝ"))]] ")"))
                  ", "
                  («term_∧_»
                   (Init.Core.«term_∈_»
                    `δ
                    " ∈ "
                    (Term.app
                     `Ioc
                     [(Term.paren "(" [(numLit "0") [(Term.typeAscription ":" (Data.Real.Basic.termℝ "ℝ"))]] ")")
                      («term_/_» (numLit "1") "/" (numLit "2"))]))
                   "∧"
                   («term_∧_»
                    (Term.forall
                     "∀"
                     [(Term.simpleBinder [`y₁ `y₂] [])
                      (Term.simpleBinder
                       [(Term.hole "_")]
                       [(Term.typeSpec
                         ":"
                         (Init.Core.«term_∈_»
                          `y₁
                          " ∈ "
                          (Init.Core.«term_∩_» (Term.app `closed_ball [`x `δ]) " ∩ " `I.Icc)))])
                      (Term.simpleBinder
                       [(Term.hole "_")]
                       [(Term.typeSpec
                         ":"
                         (Init.Core.«term_∈_»
                          `y₂
                          " ∈ "
                          (Init.Core.«term_∩_» (Term.app `closed_ball [`x `δ]) " ∩ " `I.Icc)))])]
                     ","
                     («term_≤_»
                      (Analysis.Normed.Group.Basic.«term∥_∥»
                       "∥"
                       («term_-_» (Term.app `f [`y₁]) "-" (Term.app `f [`y₂]))
                       "∥")
                      "≤"
                      («term_/_» `ε "/" (numLit "2"))))
                    "∧"
                    («term_≤_»
                     (Finset.Data.Finset.Fold.«term_*_»
                      (Cardinal.SetTheory.Cofinality.«term_^_»
                       (Finset.Data.Finset.Fold.«term_*_» (numLit "2") "*" `δ)
                       "^"
                       (Init.Logic.«term_+_» `n "+" (numLit "1")))
                      "*"
                      (Analysis.Normed.Group.Basic.«term∥_∥»
                       "∥"
                       (Term.app `f' [`x (Term.app `Pi.single [`i (numLit "1")])])
                       "∥"))
                     "≤"
                     («term_/_» `ε "/" (numLit "2")))))))]
               ":="
               (Term.byTactic
                "by"
                (Tactic.tacticSeq
                 (Tactic.tacticSeq1Indented
                  [(group
                    (Tactic.refine'
                     "refine'"
                     (Term.app
                      `eventually.and
                      [(Term.hole "_") (Term.app `eventually.and [(Term.hole "_") (Term.hole "_")])]))
                    [])
                   (group
                    (Tactic.«tactic·._»
                     "·"
                     (Tactic.tacticSeq
                      (Tactic.tacticSeq1Indented
                       [(group
                         (Tactic.exact
                          "exact"
                          (Term.app
                           `Ioc_mem_nhds_within_Ioi
                           [(Term.anonymousCtor "⟨" [`le_rfl "," `one_half_pos] "⟩")]))
                         [])])))
                    [])
                   (group
                    (Tactic.«tactic·._»
                     "·"
                     (Tactic.tacticSeq
                      (Tactic.tacticSeq1Indented
                       [(group
                         (Tactic.rcases
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
                              («term_$__» `half_pos "$" (Term.app `half_pos [`ε0]))]))]
                          ["with"
                           (Tactic.rcasesPat.tuple
                            "⟨"
                            [(Tactic.rcasesPatLo (Tactic.rcasesPatMed [(Tactic.rcasesPat.one `δ₁)]) [])
                             ","
                             (Tactic.rcasesPatLo (Tactic.rcasesPatMed [(Tactic.rcasesPat.one `δ₁0)]) [])
                             ","
                             (Tactic.rcasesPatLo (Tactic.rcasesPatMed [(Tactic.rcasesPat.one `hδ₁)]) [])]
                            "⟩")])
                         [])
                        (group
                         (Tactic.filterUpwards
                          "filter_upwards"
                          "["
                          [(Term.app `Ioc_mem_nhds_within_Ioi [(Term.anonymousCtor "⟨" [`le_rfl "," `δ₁0] "⟩")])]
                          "]"
                          [])
                         [])
                        (group
                         (Tactic.rintro
                          "rintro"
                          [(Tactic.rintroPat.one (Tactic.rcasesPat.one `δ))
                           (Tactic.rintroPat.one (Tactic.rcasesPat.one `hδ))
                           (Tactic.rintroPat.one (Tactic.rcasesPat.one `y₁))
                           (Tactic.rintroPat.one (Tactic.rcasesPat.one `y₂))
                           (Tactic.rintroPat.one (Tactic.rcasesPat.one `hy₁))
                           (Tactic.rintroPat.one (Tactic.rcasesPat.one `hy₂))]
                          [])
                         [])
                        (group
                         (Tactic.have''
                          "have"
                          []
                          [(Term.typeSpec
                            ":"
                            (Init.Core.«term_⊆_»
                             (Init.Core.«term_∩_» (Term.app `closed_ball [`x `δ]) " ∩ " `I.Icc)
                             " ⊆ "
                             (Init.Core.«term_∩_» (Term.app `closed_ball [`x `δ₁]) " ∩ " `I.Icc)))])
                         [])
                        (group
                         (Tactic.exact
                          "exact"
                          (Term.app
                           `inter_subset_inter_left
                           [(Term.hole "_")
                            (Term.app `closed_ball_subset_closed_ball [(Term.proj `hδ "." (fieldIdx "2"))])]))
                         [])
                        (group
                         (Tactic.rwSeq "rw" [] (Tactic.rwRuleSeq "[" [(Tactic.rwRule ["←"] `dist_eq_norm)] "]") [])
                         [])
                        (group
                         (tacticCalc_
                          "calc"
                          [(calcStep
                            («term_≤_»
                             (Term.app `dist [(Term.app `f [`y₁]) (Term.app `f [`y₂])])
                             "≤"
                             (Init.Logic.«term_+_»
                              (Term.app `dist [(Term.app `f [`y₁]) (Term.app `f [`x])])
                              "+"
                              (Term.app `dist [(Term.app `f [`y₂]) (Term.app `f [`x])])))
                            ":="
                            (Term.app `dist_triangle_right [(Term.hole "_") (Term.hole "_") (Term.hole "_")]))
                           (calcStep
                            («term_≤_»
                             (Term.hole "_")
                             "≤"
                             (Init.Logic.«term_+_»
                              («term_/_» («term_/_» `ε "/" (numLit "2")) "/" (numLit "2"))
                              "+"
                              («term_/_» («term_/_» `ε "/" (numLit "2")) "/" (numLit "2"))))
                            ":="
                            (Term.app
                             `add_le_add
                             [(«term_$__» (Term.app `hδ₁ [(Term.hole "_")]) "$" (Term.app `this [`hy₁]))
                              («term_$__» (Term.app `hδ₁ [(Term.hole "_")]) "$" (Term.app `this [`hy₂]))]))
                           (calcStep
                            («term_=_» (Term.hole "_") "=" («term_/_» `ε "/" (numLit "2")))
                            ":="
                            (Term.app `add_halves [(Term.hole "_")]))])
                         [])])))
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
                            [(Term.typeSpec
                              ":"
                              (Term.app
                               `ContinuousWithinAt
                               [(Term.fun
                                 "fun"
                                 (Term.basicFun
                                  [(Term.simpleBinder [`δ] [])]
                                  "=>"
                                  (Finset.Data.Finset.Fold.«term_*_»
                                   (Cardinal.SetTheory.Cofinality.«term_^_»
                                    (Finset.Data.Finset.Fold.«term_*_» (numLit "2") "*" `δ)
                                    "^"
                                    (Init.Logic.«term_+_» `n "+" (numLit "1")))
                                   "*"
                                   (Analysis.Normed.Group.Basic.«term∥_∥»
                                    "∥"
                                    (Term.app `f' [`x (Term.app `Pi.single [`i (numLit "1")])])
                                    "∥"))))
                                (Term.app
                                 `Ioi
                                 [(Term.paren
                                   "("
                                   [(numLit "0") [(Term.typeAscription ":" (Data.Real.Basic.termℝ "ℝ"))]]
                                   ")")])
                                (numLit "0")]))]
                            ":="
                            (Term.app
                             (Term.proj
                              (Term.app
                               (Term.proj (Term.app `continuous_within_at_id.const_mul [(Term.hole "_")]) "." `pow)
                               [(Term.hole "_")])
                              "."
                              `mul_const)
                             [(Term.hole "_")]))))
                         [])
                        (group
                         (Tactic.refine'
                          "refine'"
                          (Term.app `this.eventually [(Term.app `ge_mem_nhds [(Term.hole "_")])]))
                         [])
                        (group (Tactic.simpa "simpa" [] [] [] [] ["using" (Term.app `half_pos [`ε0])]) [])])))
                    [])]))))))
            [])
           (group
            (Tactic.rcases
             "rcases"
             [(Tactic.casesTarget [] `this.exists)]
             ["with"
              (Tactic.rcasesPat.tuple
               "⟨"
               [(Tactic.rcasesPatLo (Tactic.rcasesPatMed [(Tactic.rcasesPat.one `δ)]) [])
                ","
                (Tactic.rcasesPatLo
                 (Tactic.rcasesPatMed
                  [(Tactic.rcasesPat.tuple
                    "⟨"
                    [(Tactic.rcasesPatLo (Tactic.rcasesPatMed [(Tactic.rcasesPat.one `hδ0)]) [])
                     ","
                     (Tactic.rcasesPatLo (Tactic.rcasesPatMed [(Tactic.rcasesPat.one `hδ12)]) [])]
                    "⟩")])
                 [])
                ","
                (Tactic.rcasesPatLo (Tactic.rcasesPatMed [(Tactic.rcasesPat.one `hdfδ)]) [])
                ","
                (Tactic.rcasesPatLo (Tactic.rcasesPatMed [(Tactic.rcasesPat.one `hδ)]) [])]
               "⟩")])
            [])
           (group
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
                 [(Term.simpleBinder [`J `hJI `hJδ `hxJ `hJc] [])]
                 "=>"
                 (Term.subst (Term.app `add_halves [`ε]) "▸" [(Term.hole "_")])))]
              "⟩"))
            [])
           (group
            (Tactic.tacticHave_
             "have"
             (Term.haveDecl
              (Term.haveIdDecl
               [`Hl []]
               [(Term.typeSpec
                 ":"
                 (Init.Core.«term_∈_»
                  (Term.app `J.lower [`i])
                  " ∈ "
                  (Term.app `Icc [(Term.app `J.lower [`i]) (Term.app `J.upper [`i])])))]
               ":="
               (Term.app (Term.proj `Set.left_mem_Icc "." (fieldIdx "2")) [(Term.app `J.lower_le_upper [`i])]))))
            [])
           (group
            (Tactic.tacticHave_
             "have"
             (Term.haveDecl
              (Term.haveIdDecl
               [`Hu []]
               [(Term.typeSpec
                 ":"
                 (Init.Core.«term_∈_»
                  (Term.app `J.upper [`i])
                  " ∈ "
                  (Term.app `Icc [(Term.app `J.lower [`i]) (Term.app `J.upper [`i])])))]
               ":="
               (Term.app (Term.proj `Set.right_mem_Icc "." (fieldIdx "2")) [(Term.app `J.lower_le_upper [`i])]))))
            [])
           (group
            (Tactic.have''
             "have"
             [`Hi []]
             [(Term.typeSpec
               ":"
               (Term.forall
                "∀"
                []
                ","
                (Mathlib.ExtendedBinder.«term∀___,_»
                 "∀"
                 `x
                 («binderTerm∈_» "∈" (Term.app `Icc [(Term.app `J.lower [`i]) (Term.app `J.upper [`i])]))
                 ","
                 (Term.forall
                  "∀"
                  []
                  ","
                  (Term.app
                   (Term.explicitUniv `integrable ".{" [(numLit "0") "," `u "," `u] "}")
                   [(Term.app `J.face [`i])
                    (Order.BoundedOrder.«term⊥» "⊥")
                    (Term.fun
                     "fun"
                     (Term.basicFun
                      [(Term.simpleBinder [`y] [])]
                      "=>"
                      (Term.app `f [(Term.app `i.insert_nth [`x `y])])))
                    `box_additive_map.volume])))))])
            [])
           (group
            (Tactic.exact
             "exact"
             (Term.fun
              "fun"
              (Term.basicFun
               [(Term.simpleBinder [`x `hx] [])]
               "=>"
               (Term.app
                `integrable_of_continuous_on
                [(Term.hole "_")
                 (Term.app
                  `box.continuous_on_face_Icc
                  [(«term_$__» `Hc.mono "$" (Term.app (Term.proj `box.le_iff_Icc "." (fieldIdx "1")) [`hJI])) `hx])
                 `volume]))))
            [])
           (group
            (Tactic.have''
             "have"
             [`hJδ' []]
             [(Term.typeSpec
               ":"
               (Init.Core.«term_⊆_» `J.Icc " ⊆ " (Init.Core.«term_∩_» (Term.app `closed_ball [`x `δ]) " ∩ " `I.Icc)))])
            [])
           (group
            (Tactic.exact
             "exact"
             (Term.app `subset_inter [`hJδ (Term.app (Term.proj `box.le_iff_Icc "." (fieldIdx "1")) [`hJI])]))
            [])
           (group
            (Tactic.have''
             "have"
             [`Hmaps []]
             [(Term.typeSpec
               ":"
               (Term.forall
                "∀"
                []
                ","
                (Mathlib.ExtendedBinder.«term∀___,_»
                 "∀"
                 `z
                 («binderTerm∈_» "∈" (Term.app `Icc [(Term.app `J.lower [`i]) (Term.app `J.upper [`i])]))
                 ","
                 (Term.forall
                  "∀"
                  []
                  ","
                  (Term.app
                   `maps_to
                   [(Term.app `i.insert_nth [`z])
                    (Term.proj (Term.app `J.face [`i]) "." `Icc)
                    (Init.Core.«term_∩_» (Term.app `closed_ball [`x `δ]) " ∩ " `I.Icc)])))))])
            [])
           (group
            (Tactic.exact
             "exact"
             (Term.fun
              "fun"
              (Term.basicFun
               [(Term.simpleBinder [`z `hz] [])]
               "=>"
               (Term.app (Term.proj (Term.app `J.maps_to_insert_nth_face_Icc [`hz]) "." `mono) [`subset.rfl `hJδ']))))
            [])
           (group
            (Tactic.simp
             "simp"
             []
             ["only"]
             ["["
              [(Tactic.simpLemma [] [] `dist_eq_norm) "," (Tactic.simpLemma [] [] `F) "," (Tactic.simpLemma [] [] `fI)]
              "]"]
             [])
            [])
           (group (Tactic.dsimp "dsimp" [] [] [] [] []) [])
           (group
            (Tactic.rwSeq
             "rw"
             []
             (Tactic.rwRuleSeq
              "["
              [(Tactic.rwRule
                ["←"]
                (Term.app `integral_sub [(Term.app `Hi [(Term.hole "_") `Hu]) (Term.app `Hi [(Term.hole "_") `Hl])]))]
              "]")
             [])
            [])
           (group
            (Tactic.refine'
             "refine'"
             (Term.app
              (Term.proj (Term.app `norm_sub_le [(Term.hole "_") (Term.hole "_")]) "." `trans)
              [(Term.app `add_le_add [(Term.hole "_") (Term.hole "_")])]))
            [])
           (group
            (Tactic.«tactic·._»
             "·"
             (Tactic.tacticSeq
              (Tactic.tacticSeq1Indented
               [(group
                 (Tactic.simpRw
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
                 [])
                (group
                 (Tactic.refine'
                  "refine'"
                  (Term.app
                   (Term.proj
                    («term_$__»
                     (Term.app `mul_le_mul_of_nonneg_right [(Term.hole "_")])
                     "$"
                     (Term.app `norm_nonneg [(Term.hole "_")]))
                    "."
                    `trans)
                   [`hδ]))
                 [])
                (group
                 (Tactic.tacticHave_
                  "have"
                  (Term.haveDecl
                   (Term.haveIdDecl
                    []
                    [(Term.typeSpec
                      ":"
                      (Term.forall
                       "∀"
                       [(Term.simpleBinder [`j] [])]
                       ","
                       («term_≤_»
                        (Analysis.NormedSpace.LatticeOrderedGroup.«term|_|»
                         "|"
                         («term_-_» (Term.app `J.upper [`j]) "-" (Term.app `J.lower [`j]))
                         "|")
                        "≤"
                        (Finset.Data.Finset.Fold.«term_*_» (numLit "2") "*" `δ))))]
                    ":="
                    (Term.byTactic
                     "by"
                     (Tactic.tacticSeq
                      (Tactic.tacticSeq1Indented
                       [(group (Tactic.intro "intro" [`j]) [])
                        (group
                         (tacticCalc_
                          "calc"
                          [(calcStep
                            («term_≤_»
                             (Term.app `dist [(Term.app `J.upper [`j]) (Term.app `J.lower [`j])])
                             "≤"
                             (Term.app `dist [`J.upper `J.lower]))
                            ":="
                            (Term.app `dist_le_pi_dist [(Term.hole "_") (Term.hole "_") (Term.hole "_")]))
                           (calcStep
                            («term_≤_»
                             (Term.hole "_")
                             "≤"
                             (Init.Logic.«term_+_» (Term.app `dist [`J.upper `x]) "+" (Term.app `dist [`J.lower `x])))
                            ":="
                            (Term.app `dist_triangle_right [(Term.hole "_") (Term.hole "_") (Term.hole "_")]))
                           (calcStep
                            («term_≤_» (Term.hole "_") "≤" (Init.Logic.«term_+_» `δ "+" `δ))
                            ":="
                            (Term.app
                             `add_le_add
                             [(Term.app `hJδ [`J.upper_mem_Icc]) (Term.app `hJδ [`J.lower_mem_Icc])]))
                           (calcStep
                            («term_=_» (Term.hole "_") "=" (Finset.Data.Finset.Fold.«term_*_» (numLit "2") "*" `δ))
                            ":="
                            (Term.proj (Term.app `two_mul [`δ]) "." `symm))])
                         [])]))))))
                 [])
                (group
                 (tacticCalc_
                  "calc"
                  [(calcStep
                    («term_≤_»
                     (Algebra.BigOperators.Basic.«term∏_,_»
                      "∏"
                      (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `j)] []))
                      ", "
                      (Analysis.NormedSpace.LatticeOrderedGroup.«term|_|»
                       "|"
                       («term_-_» (Term.app `J.upper [`j]) "-" (Term.app `J.lower [`j]))
                       "|"))
                     "≤"
                     (Algebra.BigOperators.Basic.«term∏_,_»
                      "∏"
                      (Lean.explicitBinders
                       (Lean.unbracketedExplicitBinders
                        [(Lean.binderIdent `j)]
                        [":" (Term.app `Finₓ [(Init.Logic.«term_+_» `n "+" (numLit "1"))])]))
                      ", "
                      (Finset.Data.Finset.Fold.«term_*_» (numLit "2") "*" `δ)))
                    ":="
                    (Term.app
                     `prod_le_prod
                     [(Term.fun
                       "fun"
                       (Term.basicFun
                        [(Term.simpleBinder [(Term.hole "_") (Term.hole "_")] [])]
                        "=>"
                        (Term.app `abs_nonneg [(Term.hole "_")])))
                      (Term.fun "fun" (Term.basicFun [(Term.simpleBinder [`j `hj] [])] "=>" (Term.app `this [`j])))]))
                   (calcStep
                    («term_=_»
                     (Term.hole "_")
                     "="
                     (Cardinal.SetTheory.Cofinality.«term_^_»
                      (Finset.Data.Finset.Fold.«term_*_» (numLit "2") "*" `δ)
                      "^"
                      (Init.Logic.«term_+_» `n "+" (numLit "1"))))
                    ":="
                    (Term.byTactic
                     "by"
                     (Tactic.tacticSeq (Tactic.tacticSeq1Indented [(group (Tactic.simp "simp" [] [] [] []) [])]))))])
                 [])])))
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
                   (Term.proj
                    (Term.app
                     `norm_integral_le_of_le_const
                     [(Term.fun
                       "fun"
                       (Term.basicFun
                        [(Term.simpleBinder [`y `hy] [])]
                        "=>"
                        (Term.app
                         `hdfδ
                         [(Term.hole "_")
                          (Term.hole "_")
                          (Term.app `Hmaps [(Term.hole "_") `Hu `hy])
                          (Term.app `Hmaps [(Term.hole "_") `Hl `hy])])))
                      (Term.hole "_")])
                    "."
                    `trans)
                   [(Term.hole "_")]))
                 [])
                (group
                 (Tactic.refine'
                  "refine'"
                  (Term.app
                   (Term.proj
                    (Term.app
                     `mul_le_mul_of_nonneg_right
                     [(Term.hole "_") (Term.proj (Term.app `half_pos [`ε0]) "." `le)])
                    "."
                    `trans_eq)
                   [(Term.app `one_mulₓ [(Term.hole "_")])]))
                 [])
                (group
                 (Tactic.rwSeq
                  "rw"
                  []
                  (Tactic.rwRuleSeq
                   "["
                   [(Tactic.rwRule [] `box.coe_eq_pi)
                    ","
                    (Tactic.rwRule
                     []
                     (Term.app `Real.volume_pi_Ioc_to_real [(Term.app `box.lower_le_upper [(Term.hole "_")])]))]
                   "]")
                  [])
                 [])
                (group
                 (Tactic.refine'
                  "refine'"
                  (Term.app
                   `prod_le_one
                   [(Term.fun
                     "fun"
                     (Term.basicFun
                      [(Term.simpleBinder [(Term.hole "_") (Term.hole "_")] [])]
                      "=>"
                      («term_$__»
                       (Term.proj `sub_nonneg "." (fieldIdx "2"))
                       "$"
                       (Term.app `box.lower_le_upper [(Term.hole "_") (Term.hole "_")]))))
                    (Term.fun "fun" (Term.basicFun [(Term.simpleBinder [`j `hj] [])] "=>" (Term.hole "_")))]))
                 [])
                (group
                 (tacticCalc_
                  "calc"
                  [(calcStep
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
                   (calcStep
                    («term_≤_» (Term.hole "_") "≤" (Term.app `dist [`J.upper `J.lower]))
                    ":="
                    (Term.app `dist_le_pi_dist [`J.upper `J.lower (Term.app `i.succ_above [`j])]))
                   (calcStep
                    («term_≤_»
                     (Term.hole "_")
                     "≤"
                     (Init.Logic.«term_+_» (Term.app `dist [`J.upper `x]) "+" (Term.app `dist [`J.lower `x])))
                    ":="
                    (Term.app `dist_triangle_right [(Term.hole "_") (Term.hole "_") (Term.hole "_")]))
                   (calcStep
                    («term_≤_» (Term.hole "_") "≤" (Init.Logic.«term_+_» `δ "+" `δ))
                    ":="
                    (Term.app `add_le_add [(Term.app `hJδ [`J.upper_mem_Icc]) (Term.app `hJδ [`J.lower_mem_Icc])]))
                   (calcStep
                    («term_≤_»
                     (Term.hole "_")
                     "≤"
                     (Init.Logic.«term_+_»
                      («term_/_» (numLit "1") "/" (numLit "2"))
                      "+"
                      («term_/_» (numLit "1") "/" (numLit "2"))))
                    ":="
                    (Term.app `add_le_add [`hδ12 `hδ12]))
                   (calcStep («term_=_» (Term.hole "_") "=" (numLit "1")) ":=" (Term.app `add_halves [(numLit "1")]))])
                 [])])))
            [])])))
       [])
      (group
       (Tactic.«tactic·._»
        "·"
        (Tactic.tacticSeq
         (Tactic.tacticSeq1Indented
          [(group (Tactic.intro "intro" [`c `x `hx `ε `ε0]) [])
           (group
            (Tactic.rcases
             "rcases"
             [(Tactic.casesTarget
               []
               (Term.app `exists_pos_mul_lt [`ε0 (Finset.Data.Finset.Fold.«term_*_» (numLit "2") "*" `c)]))]
             ["with"
              (Tactic.rcasesPat.tuple
               "⟨"
               [(Tactic.rcasesPatLo (Tactic.rcasesPatMed [(Tactic.rcasesPat.one `ε')]) [])
                ","
                (Tactic.rcasesPatLo (Tactic.rcasesPatMed [(Tactic.rcasesPat.one `ε'0)]) [])
                ","
                (Tactic.rcasesPatLo (Tactic.rcasesPatMed [(Tactic.rcasesPat.one `hlt)]) [])]
               "⟩")])
            [])
           (group
            (Tactic.rcases
             "rcases"
             [(Tactic.casesTarget
               []
               (Term.app
                (Term.proj
                 (Term.proj (Term.app `nhds_within_has_basis [`nhds_basis_closed_ball (Term.hole "_")]) "." `mem_iff)
                 "."
                 (fieldIdx "1"))
                [(Term.app (Term.proj (Term.app `Hd [`x `hx]) "." `def) [`ε'0])]))]
             ["with"
              (Tactic.rcasesPat.tuple
               "⟨"
               [(Tactic.rcasesPatLo (Tactic.rcasesPatMed [(Tactic.rcasesPat.one `δ)]) [])
                ","
                (Tactic.rcasesPatLo (Tactic.rcasesPatMed [(Tactic.rcasesPat.one `δ0)]) [])
                ","
                (Tactic.rcasesPatLo (Tactic.rcasesPatMed [(Tactic.rcasesPat.one `Hδ)]) [])]
               "⟩")])
            [])
           (group
            (Tactic.refine'
             "refine'"
             (Term.anonymousCtor
              "⟨"
              [`δ
               ","
               `δ0
               ","
               (Term.fun "fun" (Term.basicFun [(Term.simpleBinder [`J `hle `hJδ `hxJ `hJc] [])] "=>" (Term.hole "_")))]
              "⟩"))
            [])
           (group
            (Tactic.simp
             "simp"
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
            [])
           (group
            (Tactic.refine'
             "refine'"
             (Term.app
              (Term.proj
               (Term.app
                `norm_volume_sub_integral_face_upper_sub_lower_smul_le
                [(Term.hole "_")
                 («term_$__» `Hc.mono "$" (Term.app (Term.proj `box.le_iff_Icc "." (fieldIdx "1")) [`hle]))
                 `hxJ
                 `ε'0
                 (Term.fun
                  "fun"
                  (Term.basicFun [(Term.simpleBinder [`y `hy] [])] "=>" (Term.app `Hδ [(Term.hole "_")])))
                 (Term.app `hJc [`rfl])])
               "."
               `trans)
              [(Term.hole "_")]))
            [])
           (group
            (Tactic.«tactic·._»
             "·"
             (Tactic.tacticSeq
              (Tactic.tacticSeq1Indented
               [(group
                 (Tactic.exact
                  "exact"
                  (Term.anonymousCtor
                   "⟨"
                   [(Term.app `hJδ [`hy]) "," (Term.app (Term.proj `box.le_iff_Icc "." (fieldIdx "1")) [`hle `hy])]
                   "⟩"))
                 [])])))
            [])
           (group
            (Tactic.«tactic·._»
             "·"
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
                      `mul_right_commₓ
                      [(Term.paren "(" [(numLit "2") [(Term.typeAscription ":" (Data.Real.Basic.termℝ "ℝ"))]] ")")]))
                    ","
                    (Tactic.rwRule ["←"] `box.volume_apply)]
                   "]")
                  [])
                 [])
                (group
                 (Tactic.exact "exact" (Term.app `mul_le_mul_of_nonneg_right [`hlt.le `Ennreal.to_real_nonneg]))
                 [])])))
            [])])))
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
   (Tactic.tacticSeq
    (Tactic.tacticSeq1Indented
     [(group (Tactic.intro "intro" [`c `x `hx `ε `ε0]) [])
      (group
       (Tactic.rcases
        "rcases"
        [(Tactic.casesTarget
          []
          (Term.app `exists_pos_mul_lt [`ε0 (Finset.Data.Finset.Fold.«term_*_» (numLit "2") "*" `c)]))]
        ["with"
         (Tactic.rcasesPat.tuple
          "⟨"
          [(Tactic.rcasesPatLo (Tactic.rcasesPatMed [(Tactic.rcasesPat.one `ε')]) [])
           ","
           (Tactic.rcasesPatLo (Tactic.rcasesPatMed [(Tactic.rcasesPat.one `ε'0)]) [])
           ","
           (Tactic.rcasesPatLo (Tactic.rcasesPatMed [(Tactic.rcasesPat.one `hlt)]) [])]
          "⟩")])
       [])
      (group
       (Tactic.rcases
        "rcases"
        [(Tactic.casesTarget
          []
          (Term.app
           (Term.proj
            (Term.proj (Term.app `nhds_within_has_basis [`nhds_basis_closed_ball (Term.hole "_")]) "." `mem_iff)
            "."
            (fieldIdx "1"))
           [(Term.app (Term.proj (Term.app `Hd [`x `hx]) "." `def) [`ε'0])]))]
        ["with"
         (Tactic.rcasesPat.tuple
          "⟨"
          [(Tactic.rcasesPatLo (Tactic.rcasesPatMed [(Tactic.rcasesPat.one `δ)]) [])
           ","
           (Tactic.rcasesPatLo (Tactic.rcasesPatMed [(Tactic.rcasesPat.one `δ0)]) [])
           ","
           (Tactic.rcasesPatLo (Tactic.rcasesPatMed [(Tactic.rcasesPat.one `Hδ)]) [])]
          "⟩")])
       [])
      (group
       (Tactic.refine'
        "refine'"
        (Term.anonymousCtor
         "⟨"
         [`δ
          ","
          `δ0
          ","
          (Term.fun "fun" (Term.basicFun [(Term.simpleBinder [`J `hle `hJδ `hxJ `hJc] [])] "=>" (Term.hole "_")))]
         "⟩"))
       [])
      (group
       (Tactic.simp
        "simp"
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
       [])
      (group
       (Tactic.refine'
        "refine'"
        (Term.app
         (Term.proj
          (Term.app
           `norm_volume_sub_integral_face_upper_sub_lower_smul_le
           [(Term.hole "_")
            («term_$__» `Hc.mono "$" (Term.app (Term.proj `box.le_iff_Icc "." (fieldIdx "1")) [`hle]))
            `hxJ
            `ε'0
            (Term.fun "fun" (Term.basicFun [(Term.simpleBinder [`y `hy] [])] "=>" (Term.app `Hδ [(Term.hole "_")])))
            (Term.app `hJc [`rfl])])
          "."
          `trans)
         [(Term.hole "_")]))
       [])
      (group
       (Tactic.«tactic·._»
        "·"
        (Tactic.tacticSeq
         (Tactic.tacticSeq1Indented
          [(group
            (Tactic.exact
             "exact"
             (Term.anonymousCtor
              "⟨"
              [(Term.app `hJδ [`hy]) "," (Term.app (Term.proj `box.le_iff_Icc "." (fieldIdx "1")) [`hle `hy])]
              "⟩"))
            [])])))
       [])
      (group
       (Tactic.«tactic·._»
        "·"
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
                 `mul_right_commₓ
                 [(Term.paren "(" [(numLit "2") [(Term.typeAscription ":" (Data.Real.Basic.termℝ "ℝ"))]] ")")]))
               ","
               (Tactic.rwRule ["←"] `box.volume_apply)]
              "]")
             [])
            [])
           (group
            (Tactic.exact "exact" (Term.app `mul_le_mul_of_nonneg_right [`hlt.le `Ennreal.to_real_nonneg]))
            [])])))
       [])])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.«tactic·._»', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq', expected 'Lean.Parser.Tactic.tacticSeq.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeq1Indented.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'group', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Tactic.«tactic·._»
   "·"
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
            `mul_right_commₓ
            [(Term.paren "(" [(numLit "2") [(Term.typeAscription ":" (Data.Real.Basic.termℝ "ℝ"))]] ")")]))
          ","
          (Tactic.rwRule ["←"] `box.volume_apply)]
         "]")
        [])
       [])
      (group (Tactic.exact "exact" (Term.app `mul_le_mul_of_nonneg_right [`hlt.le `Ennreal.to_real_nonneg])) [])])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.«tactic·._»', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq', expected 'Lean.Parser.Tactic.tacticSeq.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeq1Indented.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'group', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Tactic.exact "exact" (Term.app `mul_le_mul_of_nonneg_right [`hlt.le `Ennreal.to_real_nonneg]))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.exact', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.app `mul_le_mul_of_nonneg_right [`hlt.le `Ennreal.to_real_nonneg])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `Ennreal.to_real_nonneg
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
  `hlt.le
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `mul_le_mul_of_nonneg_right
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
       `mul_right_commₓ
       [(Term.paren "(" [(numLit "2") [(Term.typeAscription ":" (Data.Real.Basic.termℝ "ℝ"))]] ")")]))
     ","
     (Tactic.rwRule ["←"] `box.volume_apply)]
    "]")
   [])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.rwSeq', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.rwRule', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `box.volume_apply
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«←»', expected 'optional.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.rwRule', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.app
   `mul_right_commₓ
   [(Term.paren "(" [(numLit "2") [(Term.typeAscription ":" (Data.Real.Basic.termℝ "ℝ"))]] ")")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.paren', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.paren', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.paren', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.paren', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.paren', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
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
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `mul_right_commₓ
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'group', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, tactic))
  (Tactic.«tactic·._»
   "·"
   (Tactic.tacticSeq
    (Tactic.tacticSeq1Indented
     [(group
       (Tactic.exact
        "exact"
        (Term.anonymousCtor
         "⟨"
         [(Term.app `hJδ [`hy]) "," (Term.app (Term.proj `box.le_iff_Icc "." (fieldIdx "1")) [`hle `hy])]
         "⟩"))
       [])])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.«tactic·._»', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq', expected 'Lean.Parser.Tactic.tacticSeq.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeq1Indented.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'group', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Tactic.exact
   "exact"
   (Term.anonymousCtor
    "⟨"
    [(Term.app `hJδ [`hy]) "," (Term.app (Term.proj `box.le_iff_Icc "." (fieldIdx "1")) [`hle `hy])]
    "⟩"))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.exact', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.anonymousCtor
   "⟨"
   [(Term.app `hJδ [`hy]) "," (Term.app (Term.proj `box.le_iff_Icc "." (fieldIdx "1")) [`hle `hy])]
   "⟩")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.anonymousCtor', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.anonymousCtor', expected 'Lean.Parser.Term.anonymousCtor.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.app (Term.proj `box.le_iff_Icc "." (fieldIdx "1")) [`hle `hy])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `hy
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
  `hle
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  (Term.proj `box.le_iff_Icc "." (fieldIdx "1"))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.proj', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
  `box.le_iff_Icc
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.app `hJδ [`hy])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `hy
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `hJδ
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'group', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, tactic))
  (Tactic.refine'
   "refine'"
   (Term.app
    (Term.proj
     (Term.app
      `norm_volume_sub_integral_face_upper_sub_lower_smul_le
      [(Term.hole "_")
       («term_$__» `Hc.mono "$" (Term.app (Term.proj `box.le_iff_Icc "." (fieldIdx "1")) [`hle]))
       `hxJ
       `ε'0
       (Term.fun "fun" (Term.basicFun [(Term.simpleBinder [`y `hy] [])] "=>" (Term.app `Hδ [(Term.hole "_")])))
       (Term.app `hJc [`rfl])])
     "."
     `trans)
    [(Term.hole "_")]))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.refine'', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.app
   (Term.proj
    (Term.app
     `norm_volume_sub_integral_face_upper_sub_lower_smul_le
     [(Term.hole "_")
      («term_$__» `Hc.mono "$" (Term.app (Term.proj `box.le_iff_Icc "." (fieldIdx "1")) [`hle]))
      `hxJ
      `ε'0
      (Term.fun "fun" (Term.basicFun [(Term.simpleBinder [`y `hy] [])] "=>" (Term.app `Hδ [(Term.hole "_")])))
      (Term.app `hJc [`rfl])])
    "."
    `trans)
   [(Term.hole "_")])
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
  (Term.proj
   (Term.app
    `norm_volume_sub_integral_face_upper_sub_lower_smul_le
    [(Term.hole "_")
     («term_$__» `Hc.mono "$" (Term.app (Term.proj `box.le_iff_Icc "." (fieldIdx "1")) [`hle]))
     `hxJ
     `ε'0
     (Term.fun "fun" (Term.basicFun [(Term.simpleBinder [`y `hy] [])] "=>" (Term.app `Hδ [(Term.hole "_")])))
     (Term.app `hJc [`rfl])])
   "."
   `trans)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.proj', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
  (Term.app
   `norm_volume_sub_integral_face_upper_sub_lower_smul_le
   [(Term.hole "_")
    («term_$__» `Hc.mono "$" (Term.app (Term.proj `box.le_iff_Icc "." (fieldIdx "1")) [`hle]))
    `hxJ
    `ε'0
    (Term.fun "fun" (Term.basicFun [(Term.simpleBinder [`y `hy] [])] "=>" (Term.app `Hδ [(Term.hole "_")])))
    (Term.app `hJc [`rfl])])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.app `hJc [`rfl])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `rfl
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `hJc
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren "(" [(Term.app `hJc [`rfl]) []] ")")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
  (Term.fun "fun" (Term.basicFun [(Term.simpleBinder [`y `hy] [])] "=>" (Term.app `Hδ [(Term.hole "_")])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.fun.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.basicFun', expected 'Lean.Parser.Term.basicFun.antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.app `Hδ [(Term.hole "_")])
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
  `Hδ
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
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (some 0, term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
 "("
 [(Term.fun "fun" (Term.basicFun [(Term.simpleBinder [`y `hy] [])] "=>" (Term.app `Hδ [(Term.hole "_")]))) []]
 ")")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
  `ε'0
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
  `hxJ
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_$__»', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_$__»', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_$__»', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_$__»', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_$__»', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
  («term_$__» `Hc.mono "$" (Term.app (Term.proj `box.le_iff_Icc "." (fieldIdx "1")) [`hle]))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_$__»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.app (Term.proj `box.le_iff_Icc "." (fieldIdx "1")) [`hle])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `hle
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  (Term.proj `box.le_iff_Icc "." (fieldIdx "1"))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.proj', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
  `box.le_iff_Icc
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 10 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 10, term))
  `Hc.mono
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 10, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 10, (some 10, term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
 "("
 [(«term_$__» `Hc.mono "$" (Term.app (Term.proj `box.le_iff_Icc "." (fieldIdx "1")) [`hle])) []]
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
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `norm_volume_sub_integral_face_upper_sub_lower_smul_le
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
 "("
 [(Term.app
   `norm_volume_sub_integral_face_upper_sub_lower_smul_le
   [(Term.hole "_")
    (Term.paren "(" [(«term_$__» `Hc.mono "$" (Term.app (Term.proj `box.le_iff_Icc "." (fieldIdx "1")) [`hle])) []] ")")
    `hxJ
    `ε'0
    (Term.paren
     "("
     [(Term.fun "fun" (Term.basicFun [(Term.simpleBinder [`y `hy] [])] "=>" (Term.app `Hδ [(Term.hole "_")]))) []]
     ")")
    (Term.paren "(" [(Term.app `hJc [`rfl]) []] ")")])
  []]
 ")")
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'group', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, tactic))
  (Tactic.simp
   "simp"
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
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simp', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«]»', expected 'optional.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `dist_eq_norm
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `box.volume_apply
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `box_additive_map.volume_apply
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'only', expected 'optional.antiquot_scope'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'group', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, tactic))
  (Tactic.refine'
   "refine'"
   (Term.anonymousCtor
    "⟨"
    [`δ
     ","
     `δ0
     ","
     (Term.fun "fun" (Term.basicFun [(Term.simpleBinder [`J `hle `hJδ `hxJ `hJc] [])] "=>" (Term.hole "_")))]
    "⟩"))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.refine'', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.anonymousCtor
   "⟨"
   [`δ
    ","
    `δ0
    ","
    (Term.fun "fun" (Term.basicFun [(Term.simpleBinder [`J `hle `hJδ `hxJ `hJc] [])] "=>" (Term.hole "_")))]
   "⟩")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.anonymousCtor', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.anonymousCtor', expected 'Lean.Parser.Term.anonymousCtor.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.fun "fun" (Term.basicFun [(Term.simpleBinder [`J `hle `hJδ `hxJ `hJc] [])] "=>" (Term.hole "_")))
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
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `δ0
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `δ
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'group', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, tactic))
  (Tactic.rcases
   "rcases"
   [(Tactic.casesTarget
     []
     (Term.app
      (Term.proj
       (Term.proj (Term.app `nhds_within_has_basis [`nhds_basis_closed_ball (Term.hole "_")]) "." `mem_iff)
       "."
       (fieldIdx "1"))
      [(Term.app (Term.proj (Term.app `Hd [`x `hx]) "." `def) [`ε'0])]))]
   ["with"
    (Tactic.rcasesPat.tuple
     "⟨"
     [(Tactic.rcasesPatLo (Tactic.rcasesPatMed [(Tactic.rcasesPat.one `δ)]) [])
      ","
      (Tactic.rcasesPatLo (Tactic.rcasesPatMed [(Tactic.rcasesPat.one `δ0)]) [])
      ","
      (Tactic.rcasesPatLo (Tactic.rcasesPatMed [(Tactic.rcasesPat.one `Hδ)]) [])]
     "⟩")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.rcases', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.rcasesPat.tuple', expected 'optional.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.rcasesPat.tuple', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.rcasesPatLo', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.rcasesPat.one', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.rcasesPat.one', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.rcasesPatLo', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.rcasesPat.one', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.rcasesPat.one', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.rcasesPatLo', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.rcasesPat.one', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.rcasesPat.one', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.casesTarget', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.app
   (Term.proj
    (Term.proj (Term.app `nhds_within_has_basis [`nhds_basis_closed_ball (Term.hole "_")]) "." `mem_iff)
    "."
    (fieldIdx "1"))
   [(Term.app (Term.proj (Term.app `Hd [`x `hx]) "." `def) [`ε'0])])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.app (Term.proj (Term.app `Hd [`x `hx]) "." `def) [`ε'0])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `ε'0
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  (Term.proj (Term.app `Hd [`x `hx]) "." `def)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.proj', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
  (Term.app `Hd [`x `hx])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `hx
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
  `x
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `Hd
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren "(" [(Term.app `Hd [`x `hx]) []] ")")
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
 "("
 [(Term.app (Term.proj (Term.paren "(" [(Term.app `Hd [`x `hx]) []] ")") "." `def) [`ε'0]) []]
 ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  (Term.proj
   (Term.proj (Term.app `nhds_within_has_basis [`nhds_basis_closed_ball (Term.hole "_")]) "." `mem_iff)
   "."
   (fieldIdx "1"))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.proj', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
  (Term.proj (Term.app `nhds_within_has_basis [`nhds_basis_closed_ball (Term.hole "_")]) "." `mem_iff)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.proj', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
  (Term.app `nhds_within_has_basis [`nhds_basis_closed_ball (Term.hole "_")])
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
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, term))
  `nhds_basis_closed_ball
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (some 1023, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `nhds_within_has_basis
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
 "("
 [(Term.app `nhds_within_has_basis [`nhds_basis_closed_ball (Term.hole "_")]) []]
 ")")
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'group', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, tactic))
  (Tactic.rcases
   "rcases"
   [(Tactic.casesTarget [] (Term.app `exists_pos_mul_lt [`ε0 (Finset.Data.Finset.Fold.«term_*_» (numLit "2") "*" `c)]))]
   ["with"
    (Tactic.rcasesPat.tuple
     "⟨"
     [(Tactic.rcasesPatLo (Tactic.rcasesPatMed [(Tactic.rcasesPat.one `ε')]) [])
      ","
      (Tactic.rcasesPatLo (Tactic.rcasesPatMed [(Tactic.rcasesPat.one `ε'0)]) [])
      ","
      (Tactic.rcasesPatLo (Tactic.rcasesPatMed [(Tactic.rcasesPat.one `hlt)]) [])]
     "⟩")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.rcases', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.rcasesPat.tuple', expected 'optional.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.rcasesPat.tuple', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.rcasesPatLo', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.rcasesPat.one', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.rcasesPat.one', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.rcasesPatLo', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.rcasesPat.one', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.rcasesPat.one', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.rcasesPatLo', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.rcasesPat.one', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.rcasesPat.one', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.casesTarget', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.app `exists_pos_mul_lt [`ε0 (Finset.Data.Finset.Fold.«term_*_» (numLit "2") "*" `c)])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Finset.Data.Finset.Fold.«term_*_»', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Finset.Data.Finset.Fold.«term_*_»', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Finset.Data.Finset.Fold.«term_*_»', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Finset.Data.Finset.Fold.«term_*_»', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Finset.Data.Finset.Fold.«term_*_»', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Finset.Data.Finset.Fold.«term_*_» (numLit "2") "*" `c)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Finset.Data.Finset.Fold.«term_*_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `c
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  (numLit "2")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'numLit', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'numLit', expected 'numLit.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
 "("
 [(Finset.Data.Finset.Fold.«term_*_» (numLit "2") "*" `c) []]
 ")")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
  `ε0
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `exists_pos_mul_lt
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'group', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, tactic))
  (Tactic.intro "intro" [`c `x `hx `ε `ε0])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.intro', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `ε0
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
  `ε
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
  `hx
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
  `x
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
  `c
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'group', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, tactic))
  (Tactic.«tactic·._»
   "·"
   (Tactic.tacticSeq
    (Tactic.tacticSeq1Indented
     [(group (Tactic.intro "intro" [`c `x `hx `ε `ε0]) [])
      (group
       (Tactic.tacticHave_
        "have"
        (Term.haveDecl
         (Term.haveIdDecl
          []
          [(Term.typeSpec
            ":"
            (Filter.Order.Filter.Basic.«term∀ᶠ_in_,_»
             "∀ᶠ"
             (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `δ)] []))
             " in "
             (Topology.Basic.«term𝓝[>]_»
              "𝓝[>] "
              (Term.paren "(" [(numLit "0") [(Term.typeAscription ":" (Data.Real.Basic.termℝ "ℝ"))]] ")"))
             ", "
             («term_∧_»
              (Init.Core.«term_∈_»
               `δ
               " ∈ "
               (Term.app
                `Ioc
                [(Term.paren "(" [(numLit "0") [(Term.typeAscription ":" (Data.Real.Basic.termℝ "ℝ"))]] ")")
                 («term_/_» (numLit "1") "/" (numLit "2"))]))
              "∧"
              («term_∧_»
               (Term.forall
                "∀"
                [(Term.simpleBinder [`y₁ `y₂] [])
                 (Term.simpleBinder
                  [(Term.hole "_")]
                  [(Term.typeSpec
                    ":"
                    (Init.Core.«term_∈_»
                     `y₁
                     " ∈ "
                     (Init.Core.«term_∩_» (Term.app `closed_ball [`x `δ]) " ∩ " `I.Icc)))])
                 (Term.simpleBinder
                  [(Term.hole "_")]
                  [(Term.typeSpec
                    ":"
                    (Init.Core.«term_∈_»
                     `y₂
                     " ∈ "
                     (Init.Core.«term_∩_» (Term.app `closed_ball [`x `δ]) " ∩ " `I.Icc)))])]
                ","
                («term_≤_»
                 (Analysis.Normed.Group.Basic.«term∥_∥» "∥" («term_-_» (Term.app `f [`y₁]) "-" (Term.app `f [`y₂])) "∥")
                 "≤"
                 («term_/_» `ε "/" (numLit "2"))))
               "∧"
               («term_≤_»
                (Finset.Data.Finset.Fold.«term_*_»
                 (Cardinal.SetTheory.Cofinality.«term_^_»
                  (Finset.Data.Finset.Fold.«term_*_» (numLit "2") "*" `δ)
                  "^"
                  (Init.Logic.«term_+_» `n "+" (numLit "1")))
                 "*"
                 (Analysis.Normed.Group.Basic.«term∥_∥»
                  "∥"
                  (Term.app `f' [`x (Term.app `Pi.single [`i (numLit "1")])])
                  "∥"))
                "≤"
                («term_/_» `ε "/" (numLit "2")))))))]
          ":="
          (Term.byTactic
           "by"
           (Tactic.tacticSeq
            (Tactic.tacticSeq1Indented
             [(group
               (Tactic.refine'
                "refine'"
                (Term.app
                 `eventually.and
                 [(Term.hole "_") (Term.app `eventually.and [(Term.hole "_") (Term.hole "_")])]))
               [])
              (group
               (Tactic.«tactic·._»
                "·"
                (Tactic.tacticSeq
                 (Tactic.tacticSeq1Indented
                  [(group
                    (Tactic.exact
                     "exact"
                     (Term.app `Ioc_mem_nhds_within_Ioi [(Term.anonymousCtor "⟨" [`le_rfl "," `one_half_pos] "⟩")]))
                    [])])))
               [])
              (group
               (Tactic.«tactic·._»
                "·"
                (Tactic.tacticSeq
                 (Tactic.tacticSeq1Indented
                  [(group
                    (Tactic.rcases
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
                         («term_$__» `half_pos "$" (Term.app `half_pos [`ε0]))]))]
                     ["with"
                      (Tactic.rcasesPat.tuple
                       "⟨"
                       [(Tactic.rcasesPatLo (Tactic.rcasesPatMed [(Tactic.rcasesPat.one `δ₁)]) [])
                        ","
                        (Tactic.rcasesPatLo (Tactic.rcasesPatMed [(Tactic.rcasesPat.one `δ₁0)]) [])
                        ","
                        (Tactic.rcasesPatLo (Tactic.rcasesPatMed [(Tactic.rcasesPat.one `hδ₁)]) [])]
                       "⟩")])
                    [])
                   (group
                    (Tactic.filterUpwards
                     "filter_upwards"
                     "["
                     [(Term.app `Ioc_mem_nhds_within_Ioi [(Term.anonymousCtor "⟨" [`le_rfl "," `δ₁0] "⟩")])]
                     "]"
                     [])
                    [])
                   (group
                    (Tactic.rintro
                     "rintro"
                     [(Tactic.rintroPat.one (Tactic.rcasesPat.one `δ))
                      (Tactic.rintroPat.one (Tactic.rcasesPat.one `hδ))
                      (Tactic.rintroPat.one (Tactic.rcasesPat.one `y₁))
                      (Tactic.rintroPat.one (Tactic.rcasesPat.one `y₂))
                      (Tactic.rintroPat.one (Tactic.rcasesPat.one `hy₁))
                      (Tactic.rintroPat.one (Tactic.rcasesPat.one `hy₂))]
                     [])
                    [])
                   (group
                    (Tactic.have''
                     "have"
                     []
                     [(Term.typeSpec
                       ":"
                       (Init.Core.«term_⊆_»
                        (Init.Core.«term_∩_» (Term.app `closed_ball [`x `δ]) " ∩ " `I.Icc)
                        " ⊆ "
                        (Init.Core.«term_∩_» (Term.app `closed_ball [`x `δ₁]) " ∩ " `I.Icc)))])
                    [])
                   (group
                    (Tactic.exact
                     "exact"
                     (Term.app
                      `inter_subset_inter_left
                      [(Term.hole "_")
                       (Term.app `closed_ball_subset_closed_ball [(Term.proj `hδ "." (fieldIdx "2"))])]))
                    [])
                   (group (Tactic.rwSeq "rw" [] (Tactic.rwRuleSeq "[" [(Tactic.rwRule ["←"] `dist_eq_norm)] "]") []) [])
                   (group
                    (tacticCalc_
                     "calc"
                     [(calcStep
                       («term_≤_»
                        (Term.app `dist [(Term.app `f [`y₁]) (Term.app `f [`y₂])])
                        "≤"
                        (Init.Logic.«term_+_»
                         (Term.app `dist [(Term.app `f [`y₁]) (Term.app `f [`x])])
                         "+"
                         (Term.app `dist [(Term.app `f [`y₂]) (Term.app `f [`x])])))
                       ":="
                       (Term.app `dist_triangle_right [(Term.hole "_") (Term.hole "_") (Term.hole "_")]))
                      (calcStep
                       («term_≤_»
                        (Term.hole "_")
                        "≤"
                        (Init.Logic.«term_+_»
                         («term_/_» («term_/_» `ε "/" (numLit "2")) "/" (numLit "2"))
                         "+"
                         («term_/_» («term_/_» `ε "/" (numLit "2")) "/" (numLit "2"))))
                       ":="
                       (Term.app
                        `add_le_add
                        [(«term_$__» (Term.app `hδ₁ [(Term.hole "_")]) "$" (Term.app `this [`hy₁]))
                         («term_$__» (Term.app `hδ₁ [(Term.hole "_")]) "$" (Term.app `this [`hy₂]))]))
                      (calcStep
                       («term_=_» (Term.hole "_") "=" («term_/_» `ε "/" (numLit "2")))
                       ":="
                       (Term.app `add_halves [(Term.hole "_")]))])
                    [])])))
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
                       [(Term.typeSpec
                         ":"
                         (Term.app
                          `ContinuousWithinAt
                          [(Term.fun
                            "fun"
                            (Term.basicFun
                             [(Term.simpleBinder [`δ] [])]
                             "=>"
                             (Finset.Data.Finset.Fold.«term_*_»
                              (Cardinal.SetTheory.Cofinality.«term_^_»
                               (Finset.Data.Finset.Fold.«term_*_» (numLit "2") "*" `δ)
                               "^"
                               (Init.Logic.«term_+_» `n "+" (numLit "1")))
                              "*"
                              (Analysis.Normed.Group.Basic.«term∥_∥»
                               "∥"
                               (Term.app `f' [`x (Term.app `Pi.single [`i (numLit "1")])])
                               "∥"))))
                           (Term.app
                            `Ioi
                            [(Term.paren
                              "("
                              [(numLit "0") [(Term.typeAscription ":" (Data.Real.Basic.termℝ "ℝ"))]]
                              ")")])
                           (numLit "0")]))]
                       ":="
                       (Term.app
                        (Term.proj
                         (Term.app
                          (Term.proj (Term.app `continuous_within_at_id.const_mul [(Term.hole "_")]) "." `pow)
                          [(Term.hole "_")])
                         "."
                         `mul_const)
                        [(Term.hole "_")]))))
                    [])
                   (group
                    (Tactic.refine' "refine'" (Term.app `this.eventually [(Term.app `ge_mem_nhds [(Term.hole "_")])]))
                    [])
                   (group (Tactic.simpa "simpa" [] [] [] [] ["using" (Term.app `half_pos [`ε0])]) [])])))
               [])]))))))
       [])
      (group
       (Tactic.rcases
        "rcases"
        [(Tactic.casesTarget [] `this.exists)]
        ["with"
         (Tactic.rcasesPat.tuple
          "⟨"
          [(Tactic.rcasesPatLo (Tactic.rcasesPatMed [(Tactic.rcasesPat.one `δ)]) [])
           ","
           (Tactic.rcasesPatLo
            (Tactic.rcasesPatMed
             [(Tactic.rcasesPat.tuple
               "⟨"
               [(Tactic.rcasesPatLo (Tactic.rcasesPatMed [(Tactic.rcasesPat.one `hδ0)]) [])
                ","
                (Tactic.rcasesPatLo (Tactic.rcasesPatMed [(Tactic.rcasesPat.one `hδ12)]) [])]
               "⟩")])
            [])
           ","
           (Tactic.rcasesPatLo (Tactic.rcasesPatMed [(Tactic.rcasesPat.one `hdfδ)]) [])
           ","
           (Tactic.rcasesPatLo (Tactic.rcasesPatMed [(Tactic.rcasesPat.one `hδ)]) [])]
          "⟩")])
       [])
      (group
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
            [(Term.simpleBinder [`J `hJI `hJδ `hxJ `hJc] [])]
            "=>"
            (Term.subst (Term.app `add_halves [`ε]) "▸" [(Term.hole "_")])))]
         "⟩"))
       [])
      (group
       (Tactic.tacticHave_
        "have"
        (Term.haveDecl
         (Term.haveIdDecl
          [`Hl []]
          [(Term.typeSpec
            ":"
            (Init.Core.«term_∈_»
             (Term.app `J.lower [`i])
             " ∈ "
             (Term.app `Icc [(Term.app `J.lower [`i]) (Term.app `J.upper [`i])])))]
          ":="
          (Term.app (Term.proj `Set.left_mem_Icc "." (fieldIdx "2")) [(Term.app `J.lower_le_upper [`i])]))))
       [])
      (group
       (Tactic.tacticHave_
        "have"
        (Term.haveDecl
         (Term.haveIdDecl
          [`Hu []]
          [(Term.typeSpec
            ":"
            (Init.Core.«term_∈_»
             (Term.app `J.upper [`i])
             " ∈ "
             (Term.app `Icc [(Term.app `J.lower [`i]) (Term.app `J.upper [`i])])))]
          ":="
          (Term.app (Term.proj `Set.right_mem_Icc "." (fieldIdx "2")) [(Term.app `J.lower_le_upper [`i])]))))
       [])
      (group
       (Tactic.have''
        "have"
        [`Hi []]
        [(Term.typeSpec
          ":"
          (Term.forall
           "∀"
           []
           ","
           (Mathlib.ExtendedBinder.«term∀___,_»
            "∀"
            `x
            («binderTerm∈_» "∈" (Term.app `Icc [(Term.app `J.lower [`i]) (Term.app `J.upper [`i])]))
            ","
            (Term.forall
             "∀"
             []
             ","
             (Term.app
              (Term.explicitUniv `integrable ".{" [(numLit "0") "," `u "," `u] "}")
              [(Term.app `J.face [`i])
               (Order.BoundedOrder.«term⊥» "⊥")
               (Term.fun
                "fun"
                (Term.basicFun [(Term.simpleBinder [`y] [])] "=>" (Term.app `f [(Term.app `i.insert_nth [`x `y])])))
               `box_additive_map.volume])))))])
       [])
      (group
       (Tactic.exact
        "exact"
        (Term.fun
         "fun"
         (Term.basicFun
          [(Term.simpleBinder [`x `hx] [])]
          "=>"
          (Term.app
           `integrable_of_continuous_on
           [(Term.hole "_")
            (Term.app
             `box.continuous_on_face_Icc
             [(«term_$__» `Hc.mono "$" (Term.app (Term.proj `box.le_iff_Icc "." (fieldIdx "1")) [`hJI])) `hx])
            `volume]))))
       [])
      (group
       (Tactic.have''
        "have"
        [`hJδ' []]
        [(Term.typeSpec
          ":"
          (Init.Core.«term_⊆_» `J.Icc " ⊆ " (Init.Core.«term_∩_» (Term.app `closed_ball [`x `δ]) " ∩ " `I.Icc)))])
       [])
      (group
       (Tactic.exact
        "exact"
        (Term.app `subset_inter [`hJδ (Term.app (Term.proj `box.le_iff_Icc "." (fieldIdx "1")) [`hJI])]))
       [])
      (group
       (Tactic.have''
        "have"
        [`Hmaps []]
        [(Term.typeSpec
          ":"
          (Term.forall
           "∀"
           []
           ","
           (Mathlib.ExtendedBinder.«term∀___,_»
            "∀"
            `z
            («binderTerm∈_» "∈" (Term.app `Icc [(Term.app `J.lower [`i]) (Term.app `J.upper [`i])]))
            ","
            (Term.forall
             "∀"
             []
             ","
             (Term.app
              `maps_to
              [(Term.app `i.insert_nth [`z])
               (Term.proj (Term.app `J.face [`i]) "." `Icc)
               (Init.Core.«term_∩_» (Term.app `closed_ball [`x `δ]) " ∩ " `I.Icc)])))))])
       [])
      (group
       (Tactic.exact
        "exact"
        (Term.fun
         "fun"
         (Term.basicFun
          [(Term.simpleBinder [`z `hz] [])]
          "=>"
          (Term.app (Term.proj (Term.app `J.maps_to_insert_nth_face_Icc [`hz]) "." `mono) [`subset.rfl `hJδ']))))
       [])
      (group
       (Tactic.simp
        "simp"
        []
        ["only"]
        ["["
         [(Tactic.simpLemma [] [] `dist_eq_norm) "," (Tactic.simpLemma [] [] `F) "," (Tactic.simpLemma [] [] `fI)]
         "]"]
        [])
       [])
      (group (Tactic.dsimp "dsimp" [] [] [] [] []) [])
      (group
       (Tactic.rwSeq
        "rw"
        []
        (Tactic.rwRuleSeq
         "["
         [(Tactic.rwRule
           ["←"]
           (Term.app `integral_sub [(Term.app `Hi [(Term.hole "_") `Hu]) (Term.app `Hi [(Term.hole "_") `Hl])]))]
         "]")
        [])
       [])
      (group
       (Tactic.refine'
        "refine'"
        (Term.app
         (Term.proj (Term.app `norm_sub_le [(Term.hole "_") (Term.hole "_")]) "." `trans)
         [(Term.app `add_le_add [(Term.hole "_") (Term.hole "_")])]))
       [])
      (group
       (Tactic.«tactic·._»
        "·"
        (Tactic.tacticSeq
         (Tactic.tacticSeq1Indented
          [(group
            (Tactic.simpRw
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
            [])
           (group
            (Tactic.refine'
             "refine'"
             (Term.app
              (Term.proj
               («term_$__»
                (Term.app `mul_le_mul_of_nonneg_right [(Term.hole "_")])
                "$"
                (Term.app `norm_nonneg [(Term.hole "_")]))
               "."
               `trans)
              [`hδ]))
            [])
           (group
            (Tactic.tacticHave_
             "have"
             (Term.haveDecl
              (Term.haveIdDecl
               []
               [(Term.typeSpec
                 ":"
                 (Term.forall
                  "∀"
                  [(Term.simpleBinder [`j] [])]
                  ","
                  («term_≤_»
                   (Analysis.NormedSpace.LatticeOrderedGroup.«term|_|»
                    "|"
                    («term_-_» (Term.app `J.upper [`j]) "-" (Term.app `J.lower [`j]))
                    "|")
                   "≤"
                   (Finset.Data.Finset.Fold.«term_*_» (numLit "2") "*" `δ))))]
               ":="
               (Term.byTactic
                "by"
                (Tactic.tacticSeq
                 (Tactic.tacticSeq1Indented
                  [(group (Tactic.intro "intro" [`j]) [])
                   (group
                    (tacticCalc_
                     "calc"
                     [(calcStep
                       («term_≤_»
                        (Term.app `dist [(Term.app `J.upper [`j]) (Term.app `J.lower [`j])])
                        "≤"
                        (Term.app `dist [`J.upper `J.lower]))
                       ":="
                       (Term.app `dist_le_pi_dist [(Term.hole "_") (Term.hole "_") (Term.hole "_")]))
                      (calcStep
                       («term_≤_»
                        (Term.hole "_")
                        "≤"
                        (Init.Logic.«term_+_» (Term.app `dist [`J.upper `x]) "+" (Term.app `dist [`J.lower `x])))
                       ":="
                       (Term.app `dist_triangle_right [(Term.hole "_") (Term.hole "_") (Term.hole "_")]))
                      (calcStep
                       («term_≤_» (Term.hole "_") "≤" (Init.Logic.«term_+_» `δ "+" `δ))
                       ":="
                       (Term.app `add_le_add [(Term.app `hJδ [`J.upper_mem_Icc]) (Term.app `hJδ [`J.lower_mem_Icc])]))
                      (calcStep
                       («term_=_» (Term.hole "_") "=" (Finset.Data.Finset.Fold.«term_*_» (numLit "2") "*" `δ))
                       ":="
                       (Term.proj (Term.app `two_mul [`δ]) "." `symm))])
                    [])]))))))
            [])
           (group
            (tacticCalc_
             "calc"
             [(calcStep
               («term_≤_»
                (Algebra.BigOperators.Basic.«term∏_,_»
                 "∏"
                 (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `j)] []))
                 ", "
                 (Analysis.NormedSpace.LatticeOrderedGroup.«term|_|»
                  "|"
                  («term_-_» (Term.app `J.upper [`j]) "-" (Term.app `J.lower [`j]))
                  "|"))
                "≤"
                (Algebra.BigOperators.Basic.«term∏_,_»
                 "∏"
                 (Lean.explicitBinders
                  (Lean.unbracketedExplicitBinders
                   [(Lean.binderIdent `j)]
                   [":" (Term.app `Finₓ [(Init.Logic.«term_+_» `n "+" (numLit "1"))])]))
                 ", "
                 (Finset.Data.Finset.Fold.«term_*_» (numLit "2") "*" `δ)))
               ":="
               (Term.app
                `prod_le_prod
                [(Term.fun
                  "fun"
                  (Term.basicFun
                   [(Term.simpleBinder [(Term.hole "_") (Term.hole "_")] [])]
                   "=>"
                   (Term.app `abs_nonneg [(Term.hole "_")])))
                 (Term.fun "fun" (Term.basicFun [(Term.simpleBinder [`j `hj] [])] "=>" (Term.app `this [`j])))]))
              (calcStep
               («term_=_»
                (Term.hole "_")
                "="
                (Cardinal.SetTheory.Cofinality.«term_^_»
                 (Finset.Data.Finset.Fold.«term_*_» (numLit "2") "*" `δ)
                 "^"
                 (Init.Logic.«term_+_» `n "+" (numLit "1"))))
               ":="
               (Term.byTactic
                "by"
                (Tactic.tacticSeq (Tactic.tacticSeq1Indented [(group (Tactic.simp "simp" [] [] [] []) [])]))))])
            [])])))
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
              (Term.proj
               (Term.app
                `norm_integral_le_of_le_const
                [(Term.fun
                  "fun"
                  (Term.basicFun
                   [(Term.simpleBinder [`y `hy] [])]
                   "=>"
                   (Term.app
                    `hdfδ
                    [(Term.hole "_")
                     (Term.hole "_")
                     (Term.app `Hmaps [(Term.hole "_") `Hu `hy])
                     (Term.app `Hmaps [(Term.hole "_") `Hl `hy])])))
                 (Term.hole "_")])
               "."
               `trans)
              [(Term.hole "_")]))
            [])
           (group
            (Tactic.refine'
             "refine'"
             (Term.app
              (Term.proj
               (Term.app `mul_le_mul_of_nonneg_right [(Term.hole "_") (Term.proj (Term.app `half_pos [`ε0]) "." `le)])
               "."
               `trans_eq)
              [(Term.app `one_mulₓ [(Term.hole "_")])]))
            [])
           (group
            (Tactic.rwSeq
             "rw"
             []
             (Tactic.rwRuleSeq
              "["
              [(Tactic.rwRule [] `box.coe_eq_pi)
               ","
               (Tactic.rwRule
                []
                (Term.app `Real.volume_pi_Ioc_to_real [(Term.app `box.lower_le_upper [(Term.hole "_")])]))]
              "]")
             [])
            [])
           (group
            (Tactic.refine'
             "refine'"
             (Term.app
              `prod_le_one
              [(Term.fun
                "fun"
                (Term.basicFun
                 [(Term.simpleBinder [(Term.hole "_") (Term.hole "_")] [])]
                 "=>"
                 («term_$__»
                  (Term.proj `sub_nonneg "." (fieldIdx "2"))
                  "$"
                  (Term.app `box.lower_le_upper [(Term.hole "_") (Term.hole "_")]))))
               (Term.fun "fun" (Term.basicFun [(Term.simpleBinder [`j `hj] [])] "=>" (Term.hole "_")))]))
            [])
           (group
            (tacticCalc_
             "calc"
             [(calcStep
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
              (calcStep
               («term_≤_» (Term.hole "_") "≤" (Term.app `dist [`J.upper `J.lower]))
               ":="
               (Term.app `dist_le_pi_dist [`J.upper `J.lower (Term.app `i.succ_above [`j])]))
              (calcStep
               («term_≤_»
                (Term.hole "_")
                "≤"
                (Init.Logic.«term_+_» (Term.app `dist [`J.upper `x]) "+" (Term.app `dist [`J.lower `x])))
               ":="
               (Term.app `dist_triangle_right [(Term.hole "_") (Term.hole "_") (Term.hole "_")]))
              (calcStep
               («term_≤_» (Term.hole "_") "≤" (Init.Logic.«term_+_» `δ "+" `δ))
               ":="
               (Term.app `add_le_add [(Term.app `hJδ [`J.upper_mem_Icc]) (Term.app `hJδ [`J.lower_mem_Icc])]))
              (calcStep
               («term_≤_»
                (Term.hole "_")
                "≤"
                (Init.Logic.«term_+_»
                 («term_/_» (numLit "1") "/" (numLit "2"))
                 "+"
                 («term_/_» (numLit "1") "/" (numLit "2"))))
               ":="
               (Term.app `add_le_add [`hδ12 `hδ12]))
              (calcStep («term_=_» (Term.hole "_") "=" (numLit "1")) ":=" (Term.app `add_halves [(numLit "1")]))])
            [])])))
       [])])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.«tactic·._»', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq', expected 'Lean.Parser.Tactic.tacticSeq.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeq1Indented.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'group', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Tactic.«tactic·._»
   "·"
   (Tactic.tacticSeq
    (Tactic.tacticSeq1Indented
     [(group
       (Tactic.refine'
        "refine'"
        (Term.app
         (Term.proj
          (Term.app
           `norm_integral_le_of_le_const
           [(Term.fun
             "fun"
             (Term.basicFun
              [(Term.simpleBinder [`y `hy] [])]
              "=>"
              (Term.app
               `hdfδ
               [(Term.hole "_")
                (Term.hole "_")
                (Term.app `Hmaps [(Term.hole "_") `Hu `hy])
                (Term.app `Hmaps [(Term.hole "_") `Hl `hy])])))
            (Term.hole "_")])
          "."
          `trans)
         [(Term.hole "_")]))
       [])
      (group
       (Tactic.refine'
        "refine'"
        (Term.app
         (Term.proj
          (Term.app `mul_le_mul_of_nonneg_right [(Term.hole "_") (Term.proj (Term.app `half_pos [`ε0]) "." `le)])
          "."
          `trans_eq)
         [(Term.app `one_mulₓ [(Term.hole "_")])]))
       [])
      (group
       (Tactic.rwSeq
        "rw"
        []
        (Tactic.rwRuleSeq
         "["
         [(Tactic.rwRule [] `box.coe_eq_pi)
          ","
          (Tactic.rwRule [] (Term.app `Real.volume_pi_Ioc_to_real [(Term.app `box.lower_le_upper [(Term.hole "_")])]))]
         "]")
        [])
       [])
      (group
       (Tactic.refine'
        "refine'"
        (Term.app
         `prod_le_one
         [(Term.fun
           "fun"
           (Term.basicFun
            [(Term.simpleBinder [(Term.hole "_") (Term.hole "_")] [])]
            "=>"
            («term_$__»
             (Term.proj `sub_nonneg "." (fieldIdx "2"))
             "$"
             (Term.app `box.lower_le_upper [(Term.hole "_") (Term.hole "_")]))))
          (Term.fun "fun" (Term.basicFun [(Term.simpleBinder [`j `hj] [])] "=>" (Term.hole "_")))]))
       [])
      (group
       (tacticCalc_
        "calc"
        [(calcStep
          («term_≤_»
           («term_-_»
            (Term.app `J.upper [(Term.app `i.succ_above [`j])])
            "-"
            (Term.app `J.lower [(Term.app `i.succ_above [`j])]))
           "≤"
           (Term.app
            `dist
            [(Term.app `J.upper [(Term.app `i.succ_above [`j])]) (Term.app `J.lower [(Term.app `i.succ_above [`j])])]))
          ":="
          (Term.app `le_abs_self [(Term.hole "_")]))
         (calcStep
          («term_≤_» (Term.hole "_") "≤" (Term.app `dist [`J.upper `J.lower]))
          ":="
          (Term.app `dist_le_pi_dist [`J.upper `J.lower (Term.app `i.succ_above [`j])]))
         (calcStep
          («term_≤_»
           (Term.hole "_")
           "≤"
           (Init.Logic.«term_+_» (Term.app `dist [`J.upper `x]) "+" (Term.app `dist [`J.lower `x])))
          ":="
          (Term.app `dist_triangle_right [(Term.hole "_") (Term.hole "_") (Term.hole "_")]))
         (calcStep
          («term_≤_» (Term.hole "_") "≤" (Init.Logic.«term_+_» `δ "+" `δ))
          ":="
          (Term.app `add_le_add [(Term.app `hJδ [`J.upper_mem_Icc]) (Term.app `hJδ [`J.lower_mem_Icc])]))
         (calcStep
          («term_≤_»
           (Term.hole "_")
           "≤"
           (Init.Logic.«term_+_»
            («term_/_» (numLit "1") "/" (numLit "2"))
            "+"
            («term_/_» (numLit "1") "/" (numLit "2"))))
          ":="
          (Term.app `add_le_add [`hδ12 `hδ12]))
         (calcStep («term_=_» (Term.hole "_") "=" (numLit "1")) ":=" (Term.app `add_halves [(numLit "1")]))])
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
      («term_-_»
       (Term.app `J.upper [(Term.app `i.succ_above [`j])])
       "-"
       (Term.app `J.lower [(Term.app `i.succ_above [`j])]))
      "≤"
      (Term.app
       `dist
       [(Term.app `J.upper [(Term.app `i.succ_above [`j])]) (Term.app `J.lower [(Term.app `i.succ_above [`j])])]))
     ":="
     (Term.app `le_abs_self [(Term.hole "_")]))
    (calcStep
     («term_≤_» (Term.hole "_") "≤" (Term.app `dist [`J.upper `J.lower]))
     ":="
     (Term.app `dist_le_pi_dist [`J.upper `J.lower (Term.app `i.succ_above [`j])]))
    (calcStep
     («term_≤_»
      (Term.hole "_")
      "≤"
      (Init.Logic.«term_+_» (Term.app `dist [`J.upper `x]) "+" (Term.app `dist [`J.lower `x])))
     ":="
     (Term.app `dist_triangle_right [(Term.hole "_") (Term.hole "_") (Term.hole "_")]))
    (calcStep
     («term_≤_» (Term.hole "_") "≤" (Init.Logic.«term_+_» `δ "+" `δ))
     ":="
     (Term.app `add_le_add [(Term.app `hJδ [`J.upper_mem_Icc]) (Term.app `hJδ [`J.lower_mem_Icc])]))
    (calcStep
     («term_≤_»
      (Term.hole "_")
      "≤"
      (Init.Logic.«term_+_» («term_/_» (numLit "1") "/" (numLit "2")) "+" («term_/_» (numLit "1") "/" (numLit "2"))))
     ":="
     (Term.app `add_le_add [`hδ12 `hδ12]))
    (calcStep («term_=_» (Term.hole "_") "=" (numLit "1")) ":=" (Term.app `add_halves [(numLit "1")]))])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'tacticCalc_', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'calcStep', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.app `add_halves [(numLit "1")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'numLit', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'numLit', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'numLit', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'numLit', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'numLit', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (numLit "1")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'numLit', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'numLit', expected 'numLit.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `add_halves
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  («term_=_» (Term.hole "_") "=" (numLit "1"))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_=_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (numLit "1")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'numLit', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'numLit', expected 'numLit.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 50, term))
  (Term.hole "_")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.hole.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1024, (none, [anonymous]) <=? (some 50, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 50, (some 51, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'calcStep', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, term))
  (Term.app `add_le_add [`hδ12 `hδ12])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `hδ12
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
  `hδ12
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `add_le_add
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  («term_≤_»
   (Term.hole "_")
   "≤"
   (Init.Logic.«term_+_» («term_/_» (numLit "1") "/" (numLit "2")) "+" («term_/_» (numLit "1") "/" (numLit "2"))))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_≤_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Init.Logic.«term_+_» («term_/_» (numLit "1") "/" (numLit "2")) "+" («term_/_» (numLit "1") "/" (numLit "2")))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Init.Logic.«term_+_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  («term_/_» (numLit "1") "/" (numLit "2"))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_/_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (numLit "2")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'numLit', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'numLit', expected 'numLit.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 71 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 70, term))
  (numLit "1")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'numLit', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'numLit', expected 'numLit.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 70 >? 1024, (none, [anonymous]) <=? (some 70, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 70, (some 71, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  («term_/_» (numLit "1") "/" (numLit "2"))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_/_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (numLit "2")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'numLit', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'numLit', expected 'numLit.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 71 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 70, term))
  (numLit "1")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'numLit', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'numLit', expected 'numLit.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 70 >? 1024, (none, [anonymous]) <=? (some 70, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 70, (some 71, term) <=? (some 1022, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren "(" [(«term_/_» (numLit "1") "/" (numLit "2")) []] ")")
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1022, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 50, term))
  (Term.hole "_")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.hole.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1024, (none, [anonymous]) <=? (some 50, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 50, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'calcStep', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, term))
  (Term.app `add_le_add [(Term.app `hJδ [`J.upper_mem_Icc]) (Term.app `hJδ [`J.lower_mem_Icc])])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.app `hJδ [`J.lower_mem_Icc])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `J.lower_mem_Icc
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `hJδ
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren "(" [(Term.app `hJδ [`J.lower_mem_Icc]) []] ")")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
  (Term.app `hJδ [`J.upper_mem_Icc])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `J.upper_mem_Icc
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `hJδ
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023, term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren "(" [(Term.app `hJδ [`J.upper_mem_Icc]) []] ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `add_le_add
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  («term_≤_» (Term.hole "_") "≤" (Init.Logic.«term_+_» `δ "+" `δ))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_≤_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Init.Logic.«term_+_» `δ "+" `δ)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Init.Logic.«term_+_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `δ
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `δ
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1022, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 50, term))
  (Term.hole "_")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.hole.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1024, (none, [anonymous]) <=? (some 50, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 50, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'calcStep', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, term))
  (Term.app `dist_triangle_right [(Term.hole "_") (Term.hole "_") (Term.hole "_")])
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
  `dist_triangle_right
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  («term_≤_»
   (Term.hole "_")
   "≤"
   (Init.Logic.«term_+_» (Term.app `dist [`J.upper `x]) "+" (Term.app `dist [`J.lower `x])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_≤_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Init.Logic.«term_+_» (Term.app `dist [`J.upper `x]) "+" (Term.app `dist [`J.lower `x]))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Init.Logic.«term_+_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.app `dist [`J.lower `x])
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
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
  `J.lower
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `dist
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  (Term.app `dist [`J.upper `x])
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
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
  `J.upper
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `dist
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1022, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 50, term))
  (Term.hole "_")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.hole.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1024, (none, [anonymous]) <=? (some 50, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 50, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'calcStep', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, term))
  (Term.app `dist_le_pi_dist [`J.upper `J.lower (Term.app `i.succ_above [`j])])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.app `i.succ_above [`j])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `j
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `i.succ_above
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren "(" [(Term.app `i.succ_above [`j]) []] ")")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
  `J.lower
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
  `J.upper
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `dist_le_pi_dist
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  («term_≤_» (Term.hole "_") "≤" (Term.app `dist [`J.upper `J.lower]))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_≤_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.app `dist [`J.upper `J.lower])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `J.lower
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
  `J.upper
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `dist
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 50, term))
  (Term.hole "_")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.hole.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1024, (none, [anonymous]) <=? (some 50, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 50, (some 51, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'calcStep', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, term))
  (Term.app `le_abs_self [(Term.hole "_")])
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
  `le_abs_self
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
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
    [(Term.app `J.upper [(Term.app `i.succ_above [`j])]) (Term.app `J.lower [(Term.app `i.succ_above [`j])])]))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_≤_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.app
   `dist
   [(Term.app `J.upper [(Term.app `i.succ_above [`j])]) (Term.app `J.lower [(Term.app `i.succ_above [`j])])])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.app `J.lower [(Term.app `i.succ_above [`j])])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.app `i.succ_above [`j])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `j
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `i.succ_above
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren "(" [(Term.app `i.succ_above [`j]) []] ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `J.lower
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
 "("
 [(Term.app `J.lower [(Term.paren "(" [(Term.app `i.succ_above [`j]) []] ")")]) []]
 ")")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
  (Term.app `J.upper [(Term.app `i.succ_above [`j])])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.app `i.succ_above [`j])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `j
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `i.succ_above
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren "(" [(Term.app `i.succ_above [`j]) []] ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `J.upper
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023, term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
 "("
 [(Term.app `J.upper [(Term.paren "(" [(Term.app `i.succ_above [`j]) []] ")")]) []]
 ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `dist
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 50, term))
  («term_-_»
   (Term.app `J.upper [(Term.app `i.succ_above [`j])])
   "-"
   (Term.app `J.lower [(Term.app `i.succ_above [`j])]))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_-_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.app `J.lower [(Term.app `i.succ_above [`j])])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.app `i.succ_above [`j])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `j
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `i.succ_above
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren "(" [(Term.app `i.succ_above [`j]) []] ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `J.lower
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 66 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 65, term))
  (Term.app `J.upper [(Term.app `i.succ_above [`j])])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.app `i.succ_above [`j])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `j
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `i.succ_above
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren "(" [(Term.app `i.succ_above [`j]) []] ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `J.upper
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 65 >? 1022, (some 1023, term) <=? (some 65, term)
[PrettyPrinter.parenthesize] ...precedences are 51 >? 65, (some 66, term) <=? (some 50, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 50, (some 51, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'group', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, tactic))
  (Tactic.refine'
   "refine'"
   (Term.app
    `prod_le_one
    [(Term.fun
      "fun"
      (Term.basicFun
       [(Term.simpleBinder [(Term.hole "_") (Term.hole "_")] [])]
       "=>"
       («term_$__»
        (Term.proj `sub_nonneg "." (fieldIdx "2"))
        "$"
        (Term.app `box.lower_le_upper [(Term.hole "_") (Term.hole "_")]))))
     (Term.fun "fun" (Term.basicFun [(Term.simpleBinder [`j `hj] [])] "=>" (Term.hole "_")))]))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.refine'', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.app
   `prod_le_one
   [(Term.fun
     "fun"
     (Term.basicFun
      [(Term.simpleBinder [(Term.hole "_") (Term.hole "_")] [])]
      "=>"
      («term_$__»
       (Term.proj `sub_nonneg "." (fieldIdx "2"))
       "$"
       (Term.app `box.lower_le_upper [(Term.hole "_") (Term.hole "_")]))))
    (Term.fun "fun" (Term.basicFun [(Term.simpleBinder [`j `hj] [])] "=>" (Term.hole "_")))])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.fun "fun" (Term.basicFun [(Term.simpleBinder [`j `hj] [])] "=>" (Term.hole "_")))
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
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, term))
  (Term.fun
   "fun"
   (Term.basicFun
    [(Term.simpleBinder [(Term.hole "_") (Term.hole "_")] [])]
    "=>"
    («term_$__»
     (Term.proj `sub_nonneg "." (fieldIdx "2"))
     "$"
     (Term.app `box.lower_le_upper [(Term.hole "_") (Term.hole "_")]))))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.fun.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.basicFun', expected 'Lean.Parser.Term.basicFun.antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  («term_$__»
   (Term.proj `sub_nonneg "." (fieldIdx "2"))
   "$"
   (Term.app `box.lower_le_upper [(Term.hole "_") (Term.hole "_")]))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_$__»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.app `box.lower_le_upper [(Term.hole "_") (Term.hole "_")])
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
  `box.lower_le_upper
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 10 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 10, term))
  (Term.proj `sub_nonneg "." (fieldIdx "2"))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.proj', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
  `sub_nonneg
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 10, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 10, (some 10, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.simpleBinder', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.simpleBinder', expected 'Lean.Parser.Term.strictImplicitBinder.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.simpleBinder', expected 'Lean.Parser.Term.strictImplicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.simpleBinder', expected 'Lean.Parser.Term.implicitBinder.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.simpleBinder', expected 'Lean.Parser.Term.implicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.simpleBinder', expected 'Lean.Parser.Term.instBinder.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.simpleBinder', expected 'Lean.Parser.Term.instBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.simpleBinder', expected 'Lean.Parser.Term.simpleBinder.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'ident.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (some 0, term) <=? (some 1023, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
 "("
 [(Term.fun
   "fun"
   (Term.basicFun
    [(Term.simpleBinder [(Term.hole "_") (Term.hole "_")] [])]
    "=>"
    («term_$__»
     (Term.proj `sub_nonneg "." (fieldIdx "2"))
     "$"
     (Term.app `box.lower_le_upper [(Term.hole "_") (Term.hole "_")]))))
  []]
 ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `prod_le_one
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
   (Tactic.rwRuleSeq
    "["
    [(Tactic.rwRule [] `box.coe_eq_pi)
     ","
     (Tactic.rwRule [] (Term.app `Real.volume_pi_Ioc_to_real [(Term.app `box.lower_le_upper [(Term.hole "_")])]))]
    "]")
   [])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.rwSeq', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.rwRule', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.app `Real.volume_pi_Ioc_to_real [(Term.app `box.lower_le_upper [(Term.hole "_")])])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.app `box.lower_le_upper [(Term.hole "_")])
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
  `box.lower_le_upper
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren "(" [(Term.app `box.lower_le_upper [(Term.hole "_")]) []] ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `Real.volume_pi_Ioc_to_real
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.rwRule', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `box.coe_eq_pi
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'group', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, tactic))
  (Tactic.refine'
   "refine'"
   (Term.app
    (Term.proj
     (Term.app `mul_le_mul_of_nonneg_right [(Term.hole "_") (Term.proj (Term.app `half_pos [`ε0]) "." `le)])
     "."
     `trans_eq)
    [(Term.app `one_mulₓ [(Term.hole "_")])]))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.refine'', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.app
   (Term.proj
    (Term.app `mul_le_mul_of_nonneg_right [(Term.hole "_") (Term.proj (Term.app `half_pos [`ε0]) "." `le)])
    "."
    `trans_eq)
   [(Term.app `one_mulₓ [(Term.hole "_")])])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.app `one_mulₓ [(Term.hole "_")])
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
  `one_mulₓ
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren "(" [(Term.app `one_mulₓ [(Term.hole "_")]) []] ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  (Term.proj
   (Term.app `mul_le_mul_of_nonneg_right [(Term.hole "_") (Term.proj (Term.app `half_pos [`ε0]) "." `le)])
   "."
   `trans_eq)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.proj', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
  (Term.app `mul_le_mul_of_nonneg_right [(Term.hole "_") (Term.proj (Term.app `half_pos [`ε0]) "." `le)])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.proj', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.proj', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.proj', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.proj', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.proj', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.proj (Term.app `half_pos [`ε0]) "." `le)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.proj', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
  (Term.app `half_pos [`ε0])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `ε0
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `half_pos
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren "(" [(Term.app `half_pos [`ε0]) []] ")")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
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
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `mul_le_mul_of_nonneg_right
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
 "("
 [(Term.app
   `mul_le_mul_of_nonneg_right
   [(Term.hole "_") (Term.proj (Term.paren "(" [(Term.app `half_pos [`ε0]) []] ")") "." `le)])
  []]
 ")")
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'group', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, tactic))
  (Tactic.refine'
   "refine'"
   (Term.app
    (Term.proj
     (Term.app
      `norm_integral_le_of_le_const
      [(Term.fun
        "fun"
        (Term.basicFun
         [(Term.simpleBinder [`y `hy] [])]
         "=>"
         (Term.app
          `hdfδ
          [(Term.hole "_")
           (Term.hole "_")
           (Term.app `Hmaps [(Term.hole "_") `Hu `hy])
           (Term.app `Hmaps [(Term.hole "_") `Hl `hy])])))
       (Term.hole "_")])
     "."
     `trans)
    [(Term.hole "_")]))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.refine'', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.app
   (Term.proj
    (Term.app
     `norm_integral_le_of_le_const
     [(Term.fun
       "fun"
       (Term.basicFun
        [(Term.simpleBinder [`y `hy] [])]
        "=>"
        (Term.app
         `hdfδ
         [(Term.hole "_")
          (Term.hole "_")
          (Term.app `Hmaps [(Term.hole "_") `Hu `hy])
          (Term.app `Hmaps [(Term.hole "_") `Hl `hy])])))
      (Term.hole "_")])
    "."
    `trans)
   [(Term.hole "_")])
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
  (Term.proj
   (Term.app
    `norm_integral_le_of_le_const
    [(Term.fun
      "fun"
      (Term.basicFun
       [(Term.simpleBinder [`y `hy] [])]
       "=>"
       (Term.app
        `hdfδ
        [(Term.hole "_")
         (Term.hole "_")
         (Term.app `Hmaps [(Term.hole "_") `Hu `hy])
         (Term.app `Hmaps [(Term.hole "_") `Hl `hy])])))
     (Term.hole "_")])
   "."
   `trans)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.proj', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
  (Term.app
   `norm_integral_le_of_le_const
   [(Term.fun
     "fun"
     (Term.basicFun
      [(Term.simpleBinder [`y `hy] [])]
      "=>"
      (Term.app
       `hdfδ
       [(Term.hole "_")
        (Term.hole "_")
        (Term.app `Hmaps [(Term.hole "_") `Hu `hy])
        (Term.app `Hmaps [(Term.hole "_") `Hl `hy])])))
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
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, term))
  (Term.fun
   "fun"
   (Term.basicFun
    [(Term.simpleBinder [`y `hy] [])]
    "=>"
    (Term.app
     `hdfδ
     [(Term.hole "_")
      (Term.hole "_")
      (Term.app `Hmaps [(Term.hole "_") `Hu `hy])
      (Term.app `Hmaps [(Term.hole "_") `Hl `hy])])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.fun.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.basicFun', expected 'Lean.Parser.Term.basicFun.antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.app
   `hdfδ
   [(Term.hole "_")
    (Term.hole "_")
    (Term.app `Hmaps [(Term.hole "_") `Hu `hy])
    (Term.app `Hmaps [(Term.hole "_") `Hl `hy])])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.app `Hmaps [(Term.hole "_") `Hl `hy])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `hy
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
  `Hl
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (some 1024, term)
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
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `Hmaps
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren "(" [(Term.app `Hmaps [(Term.hole "_") `Hl `hy]) []] ")")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
  (Term.app `Hmaps [(Term.hole "_") `Hu `hy])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `hy
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
  `Hu
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (some 1024, term)
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
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `Hmaps
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023, term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren "(" [(Term.app `Hmaps [(Term.hole "_") `Hu `hy]) []] ")")
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
  `hdfδ
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
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (some 0, term) <=? (some 1023, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
 "("
 [(Term.fun
   "fun"
   (Term.basicFun
    [(Term.simpleBinder [`y `hy] [])]
    "=>"
    (Term.app
     `hdfδ
     [(Term.hole "_")
      (Term.hole "_")
      (Term.paren "(" [(Term.app `Hmaps [(Term.hole "_") `Hu `hy]) []] ")")
      (Term.paren "(" [(Term.app `Hmaps [(Term.hole "_") `Hl `hy]) []] ")")])))
  []]
 ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `norm_integral_le_of_le_const
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
 "("
 [(Term.app
   `norm_integral_le_of_le_const
   [(Term.paren
     "("
     [(Term.fun
       "fun"
       (Term.basicFun
        [(Term.simpleBinder [`y `hy] [])]
        "=>"
        (Term.app
         `hdfδ
         [(Term.hole "_")
          (Term.hole "_")
          (Term.paren "(" [(Term.app `Hmaps [(Term.hole "_") `Hu `hy]) []] ")")
          (Term.paren "(" [(Term.app `Hmaps [(Term.hole "_") `Hl `hy]) []] ")")])))
      []]
     ")")
    (Term.hole "_")])
  []]
 ")")
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'group', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, tactic))
  (Tactic.«tactic·._»
   "·"
   (Tactic.tacticSeq
    (Tactic.tacticSeq1Indented
     [(group
       (Tactic.simpRw
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
       [])
      (group
       (Tactic.refine'
        "refine'"
        (Term.app
         (Term.proj
          («term_$__»
           (Term.app `mul_le_mul_of_nonneg_right [(Term.hole "_")])
           "$"
           (Term.app `norm_nonneg [(Term.hole "_")]))
          "."
          `trans)
         [`hδ]))
       [])
      (group
       (Tactic.tacticHave_
        "have"
        (Term.haveDecl
         (Term.haveIdDecl
          []
          [(Term.typeSpec
            ":"
            (Term.forall
             "∀"
             [(Term.simpleBinder [`j] [])]
             ","
             («term_≤_»
              (Analysis.NormedSpace.LatticeOrderedGroup.«term|_|»
               "|"
               («term_-_» (Term.app `J.upper [`j]) "-" (Term.app `J.lower [`j]))
               "|")
              "≤"
              (Finset.Data.Finset.Fold.«term_*_» (numLit "2") "*" `δ))))]
          ":="
          (Term.byTactic
           "by"
           (Tactic.tacticSeq
            (Tactic.tacticSeq1Indented
             [(group (Tactic.intro "intro" [`j]) [])
              (group
               (tacticCalc_
                "calc"
                [(calcStep
                  («term_≤_»
                   (Term.app `dist [(Term.app `J.upper [`j]) (Term.app `J.lower [`j])])
                   "≤"
                   (Term.app `dist [`J.upper `J.lower]))
                  ":="
                  (Term.app `dist_le_pi_dist [(Term.hole "_") (Term.hole "_") (Term.hole "_")]))
                 (calcStep
                  («term_≤_»
                   (Term.hole "_")
                   "≤"
                   (Init.Logic.«term_+_» (Term.app `dist [`J.upper `x]) "+" (Term.app `dist [`J.lower `x])))
                  ":="
                  (Term.app `dist_triangle_right [(Term.hole "_") (Term.hole "_") (Term.hole "_")]))
                 (calcStep
                  («term_≤_» (Term.hole "_") "≤" (Init.Logic.«term_+_» `δ "+" `δ))
                  ":="
                  (Term.app `add_le_add [(Term.app `hJδ [`J.upper_mem_Icc]) (Term.app `hJδ [`J.lower_mem_Icc])]))
                 (calcStep
                  («term_=_» (Term.hole "_") "=" (Finset.Data.Finset.Fold.«term_*_» (numLit "2") "*" `δ))
                  ":="
                  (Term.proj (Term.app `two_mul [`δ]) "." `symm))])
               [])]))))))
       [])
      (group
       (tacticCalc_
        "calc"
        [(calcStep
          («term_≤_»
           (Algebra.BigOperators.Basic.«term∏_,_»
            "∏"
            (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `j)] []))
            ", "
            (Analysis.NormedSpace.LatticeOrderedGroup.«term|_|»
             "|"
             («term_-_» (Term.app `J.upper [`j]) "-" (Term.app `J.lower [`j]))
             "|"))
           "≤"
           (Algebra.BigOperators.Basic.«term∏_,_»
            "∏"
            (Lean.explicitBinders
             (Lean.unbracketedExplicitBinders
              [(Lean.binderIdent `j)]
              [":" (Term.app `Finₓ [(Init.Logic.«term_+_» `n "+" (numLit "1"))])]))
            ", "
            (Finset.Data.Finset.Fold.«term_*_» (numLit "2") "*" `δ)))
          ":="
          (Term.app
           `prod_le_prod
           [(Term.fun
             "fun"
             (Term.basicFun
              [(Term.simpleBinder [(Term.hole "_") (Term.hole "_")] [])]
              "=>"
              (Term.app `abs_nonneg [(Term.hole "_")])))
            (Term.fun "fun" (Term.basicFun [(Term.simpleBinder [`j `hj] [])] "=>" (Term.app `this [`j])))]))
         (calcStep
          («term_=_»
           (Term.hole "_")
           "="
           (Cardinal.SetTheory.Cofinality.«term_^_»
            (Finset.Data.Finset.Fold.«term_*_» (numLit "2") "*" `δ)
            "^"
            (Init.Logic.«term_+_» `n "+" (numLit "1"))))
          ":="
          (Term.byTactic
           "by"
           (Tactic.tacticSeq (Tactic.tacticSeq1Indented [(group (Tactic.simp "simp" [] [] [] []) [])]))))])
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
      (Algebra.BigOperators.Basic.«term∏_,_»
       "∏"
       (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `j)] []))
       ", "
       (Analysis.NormedSpace.LatticeOrderedGroup.«term|_|»
        "|"
        («term_-_» (Term.app `J.upper [`j]) "-" (Term.app `J.lower [`j]))
        "|"))
      "≤"
      (Algebra.BigOperators.Basic.«term∏_,_»
       "∏"
       (Lean.explicitBinders
        (Lean.unbracketedExplicitBinders
         [(Lean.binderIdent `j)]
         [":" (Term.app `Finₓ [(Init.Logic.«term_+_» `n "+" (numLit "1"))])]))
       ", "
       (Finset.Data.Finset.Fold.«term_*_» (numLit "2") "*" `δ)))
     ":="
     (Term.app
      `prod_le_prod
      [(Term.fun
        "fun"
        (Term.basicFun
         [(Term.simpleBinder [(Term.hole "_") (Term.hole "_")] [])]
         "=>"
         (Term.app `abs_nonneg [(Term.hole "_")])))
       (Term.fun "fun" (Term.basicFun [(Term.simpleBinder [`j `hj] [])] "=>" (Term.app `this [`j])))]))
    (calcStep
     («term_=_»
      (Term.hole "_")
      "="
      (Cardinal.SetTheory.Cofinality.«term_^_»
       (Finset.Data.Finset.Fold.«term_*_» (numLit "2") "*" `δ)
       "^"
       (Init.Logic.«term_+_» `n "+" (numLit "1"))))
     ":="
     (Term.byTactic
      "by"
      (Tactic.tacticSeq (Tactic.tacticSeq1Indented [(group (Tactic.simp "simp" [] [] [] []) [])]))))])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'tacticCalc_', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'calcStep', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.byTactic "by" (Tactic.tacticSeq (Tactic.tacticSeq1Indented [(group (Tactic.simp "simp" [] [] [] []) [])])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.byTactic', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.byTactic', expected 'Lean.Parser.Term.byTactic.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq', expected 'Lean.Parser.Tactic.tacticSeq.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeq1Indented.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'group', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Tactic.simp "simp" [] [] [] [])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simp', expected 'antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, tactic) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  («term_=_»
   (Term.hole "_")
   "="
   (Cardinal.SetTheory.Cofinality.«term_^_»
    (Finset.Data.Finset.Fold.«term_*_» (numLit "2") "*" `δ)
    "^"
    (Init.Logic.«term_+_» `n "+" (numLit "1"))))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_=_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Cardinal.SetTheory.Cofinality.«term_^_»
   (Finset.Data.Finset.Fold.«term_*_» (numLit "2") "*" `δ)
   "^"
   (Init.Logic.«term_+_» `n "+" (numLit "1")))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Cardinal.SetTheory.Cofinality.«term_^_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Init.Logic.«term_+_» `n "+" (numLit "1"))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Init.Logic.«term_+_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (numLit "1")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'numLit', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'numLit', expected 'numLit.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `n
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 0, term))
  (Finset.Data.Finset.Fold.«term_*_» (numLit "2") "*" `δ)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Finset.Data.Finset.Fold.«term_*_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `δ
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  (numLit "2")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'numLit', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'numLit', expected 'numLit.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1 >? 1022, (some 0, term) <=? (some 0, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
 "("
 [(Finset.Data.Finset.Fold.«term_*_» (numLit "2") "*" `δ) []]
 ")")
[PrettyPrinter.parenthesize] ...precedences are 51 >? 0, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
 "("
 [(Cardinal.SetTheory.Cofinality.«term_^_»
   (Term.paren "(" [(Finset.Data.Finset.Fold.«term_*_» (numLit "2") "*" `δ) []] ")")
   "^"
   (Init.Logic.«term_+_» `n "+" (numLit "1")))
  []]
 ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 50, term))
  (Term.hole "_")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.hole.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1024, (none, [anonymous]) <=? (some 50, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 50, (some 51, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'calcStep', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, term))
  (Term.app
   `prod_le_prod
   [(Term.fun
     "fun"
     (Term.basicFun
      [(Term.simpleBinder [(Term.hole "_") (Term.hole "_")] [])]
      "=>"
      (Term.app `abs_nonneg [(Term.hole "_")])))
    (Term.fun "fun" (Term.basicFun [(Term.simpleBinder [`j `hj] [])] "=>" (Term.app `this [`j])))])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.fun "fun" (Term.basicFun [(Term.simpleBinder [`j `hj] [])] "=>" (Term.app `this [`j])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.fun.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.basicFun', expected 'Lean.Parser.Term.basicFun.antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.app `this [`j])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `j
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `this
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
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, term))
  (Term.fun
   "fun"
   (Term.basicFun
    [(Term.simpleBinder [(Term.hole "_") (Term.hole "_")] [])]
    "=>"
    (Term.app `abs_nonneg [(Term.hole "_")])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.fun.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.basicFun', expected 'Lean.Parser.Term.basicFun.antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.app `abs_nonneg [(Term.hole "_")])
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
  `abs_nonneg
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
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'ident.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (some 0, term) <=? (some 1023, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
 "("
 [(Term.fun
   "fun"
   (Term.basicFun
    [(Term.simpleBinder [(Term.hole "_") (Term.hole "_")] [])]
    "=>"
    (Term.app `abs_nonneg [(Term.hole "_")])))
  []]
 ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `prod_le_prod
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, term) <=? (none, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  («term_≤_»
   (Algebra.BigOperators.Basic.«term∏_,_»
    "∏"
    (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `j)] []))
    ", "
    (Analysis.NormedSpace.LatticeOrderedGroup.«term|_|»
     "|"
     («term_-_» (Term.app `J.upper [`j]) "-" (Term.app `J.lower [`j]))
     "|"))
   "≤"
   (Algebra.BigOperators.Basic.«term∏_,_»
    "∏"
    (Lean.explicitBinders
     (Lean.unbracketedExplicitBinders
      [(Lean.binderIdent `j)]
      [":" (Term.app `Finₓ [(Init.Logic.«term_+_» `n "+" (numLit "1"))])]))
    ", "
    (Finset.Data.Finset.Fold.«term_*_» (numLit "2") "*" `δ)))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_≤_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Algebra.BigOperators.Basic.«term∏_,_»
   "∏"
   (Lean.explicitBinders
    (Lean.unbracketedExplicitBinders
     [(Lean.binderIdent `j)]
     [":" (Term.app `Finₓ [(Init.Logic.«term_+_» `n "+" (numLit "1"))])]))
   ", "
   (Finset.Data.Finset.Fold.«term_*_» (numLit "2") "*" `δ))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Algebra.BigOperators.Basic.«term∏_,_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Finset.Data.Finset.Fold.«term_*_» (numLit "2") "*" `δ)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Finset.Data.Finset.Fold.«term_*_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `δ
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  (numLit "2")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'numLit', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'numLit', expected 'numLit.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.explicitBinders', expected 'Mathlib.ExtendedBinder.extBinders'
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
    If `f : ℝⁿ⁺¹ → E` is differentiable on a closed rectangular box `I` with derivative `f'`, then
    the partial derivative `λ x, f' x (pi.single i 1)` is Henstock-Kurzweil integrable with integral
    equal to the difference of integrals of `f` over the faces `x i = I.upper i` and `x i = I.lower i`.
    
    More precisely, we use a non-standard generalization of the Henstock-Kurzweil integral and
    we allow `f` to be non-differentiable (but still continuous) at a countable set of points.
    
    TODO: If `n > 0`, then the condition at `x ∈ s` can be replaced by a much weaker estimate but this
    requires either better integrability theorems, or usage of a filter depending on the countable set
    `s` (we need to ensure that none of the faces of a partition contain a point from `s`). -/
  theorem
    has_integral_bot_pderiv
    ( f : ℝⁿ⁺¹ → E )
        ( f' : ℝⁿ⁺¹ → ℝⁿ⁺¹ →L[ ℝ ] E )
        ( s : Set ℝⁿ⁺¹ )
        ( hs : countable s )
        ( Hs : ∀ , ∀ x ∈ s , ∀ , ContinuousWithinAt f I.Icc x )
        ( Hd : ∀ , ∀ x ∈ I.Icc \ s , ∀ , HasFderivWithinAt f f' x I.Icc x )
        ( i : Finₓ n + 1 )
      :
        has_integral .{ 0 , u , u }
          I
            ⊥
            fun x => f' x Pi.single i 1
            box_additive_map.volume
            integral .{ 0 , u , u } I.face i ⊥ fun x => f i.insert_nth I.upper i x box_additive_map.volume
              -
              integral .{ 0 , u , u } I.face i ⊥ fun x => f i.insert_nth I.lower i x box_additive_map.volume
    :=
      by
        have
            Hc
              : ContinuousOn f I.Icc
              :=
              by intro x hx by_cases' hxs : x ∈ s exacts [ Hs x hxs , Hd x ⟨ hx , hxs ⟩ . ContinuousWithinAt ]
          set
            fI
            : ℝ → box Finₓ n → E
            :=
            fun y J => integral .{ 0 , u , u } J ⊥ fun x => f i.insert_nth y x box_additive_map.volume
          set
            fb
            : Icc I.lower i I.upper i → Finₓ n →ᵇᵃ[ ↑ I.face i ] E
            :=
            fun x => integrable_of_continuous_on ⊥ box.continuous_on_face_Icc Hc x . 2 volume . toBoxAdditive
          set F : Finₓ n + 1 →ᵇᵃ[ I ] E := box_additive_map.upper_sub_lower I i fI fb fun x hx J => rfl
          change has_integral I ⊥ fun x => f' x Pi.single i 1 _ F I
          refine' has_integral_of_le_Henstock_of_forall_is_o bot_le _ _ _ s hs _ _
          · exact ( volume : Measureₓ ℝⁿ⁺¹ ) . toBoxAdditive . restrict _ le_top
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
                            y₁ y₂ _ : y₁ ∈ closed_ball x δ ∩ I.Icc _ : y₂ ∈ closed_ball x δ ∩ I.Icc
                            ,
                            ∥ f y₁ - f y₂ ∥ ≤ ε / 2
                          ∧
                          2 * δ ^ n + 1 * ∥ f' x Pi.single i 1 ∥ ≤ ε / 2
                  :=
                  by
                    refine' eventually.and _ eventually.and _ _
                      · exact Ioc_mem_nhds_within_Ioi ⟨ le_rfl , one_half_pos ⟩
                      ·
                        rcases
                            nhds_within_has_basis nhds_basis_closed_ball _ . tendsto_iff nhds_basis_closed_ball . 1
                              Hs x hx . 2 _ half_pos $ half_pos ε0
                            with ⟨ δ₁ , δ₁0 , hδ₁ ⟩
                          filter_upwards [ Ioc_mem_nhds_within_Ioi ⟨ le_rfl , δ₁0 ⟩ ]
                          rintro δ hδ y₁ y₂ hy₁ hy₂
                          have : closed_ball x δ ∩ I.Icc ⊆ closed_ball x δ₁ ∩ I.Icc
                          exact inter_subset_inter_left _ closed_ball_subset_closed_ball hδ . 2
                          rw [ ← dist_eq_norm ]
                          calc
                            dist f y₁ f y₂ ≤ dist f y₁ f x + dist f y₂ f x := dist_triangle_right _ _ _
                              _ ≤ ε / 2 / 2 + ε / 2 / 2 := add_le_add hδ₁ _ $ this hy₁ hδ₁ _ $ this hy₂
                              _ = ε / 2 := add_halves _
                      ·
                        have
                            : ContinuousWithinAt fun δ => 2 * δ ^ n + 1 * ∥ f' x Pi.single i 1 ∥ Ioi ( 0 : ℝ ) 0
                              :=
                              continuous_within_at_id.const_mul _ . pow _ . mul_const _
                          refine' this.eventually ge_mem_nhds _
                          simpa using half_pos ε0
              rcases this.exists with ⟨ δ , ⟨ hδ0 , hδ12 ⟩ , hdfδ , hδ ⟩
              refine' ⟨ δ , hδ0 , fun J hJI hJδ hxJ hJc => add_halves ε ▸ _ ⟩
              have Hl : J.lower i ∈ Icc J.lower i J.upper i := Set.left_mem_Icc . 2 J.lower_le_upper i
              have Hu : J.upper i ∈ Icc J.lower i J.upper i := Set.right_mem_Icc . 2 J.lower_le_upper i
              have
                Hi
                :
                  ∀
                    ,
                    ∀
                      x
                      ∈ Icc J.lower i J.upper i
                      ,
                      ∀ , integrable .{ 0 , u , u } J.face i ⊥ fun y => f i.insert_nth x y box_additive_map.volume
              exact
                fun
                  x hx
                    =>
                    integrable_of_continuous_on _ box.continuous_on_face_Icc Hc.mono $ box.le_iff_Icc . 1 hJI hx volume
              have hJδ' : J.Icc ⊆ closed_ball x δ ∩ I.Icc
              exact subset_inter hJδ box.le_iff_Icc . 1 hJI
              have
                Hmaps
                : ∀ , ∀ z ∈ Icc J.lower i J.upper i , ∀ , maps_to i.insert_nth z J.face i . Icc closed_ball x δ ∩ I.Icc
              exact fun z hz => J.maps_to_insert_nth_face_Icc hz . mono subset.rfl hJδ'
              simp only [ dist_eq_norm , F , fI ]
              dsimp
              rw [ ← integral_sub Hi _ Hu Hi _ Hl ]
              refine' norm_sub_le _ _ . trans add_le_add _ _
              ·
                simp_rw [ box_additive_map.volume_apply , norm_smul , Real.norm_eq_abs , abs_prod ]
                  refine' mul_le_mul_of_nonneg_right _ $ norm_nonneg _ . trans hδ
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
                    ∏ j , | J.upper j - J.lower j | ≤ ∏ j : Finₓ n + 1 , 2 * δ
                        :=
                        prod_le_prod fun _ _ => abs_nonneg _ fun j hj => this j
                      _ = 2 * δ ^ n + 1 := by simp
              ·
                refine' norm_integral_le_of_le_const fun y hy => hdfδ _ _ Hmaps _ Hu hy Hmaps _ Hl hy _ . trans _
                  refine' mul_le_mul_of_nonneg_right _ half_pos ε0 . le . trans_eq one_mulₓ _
                  rw [ box.coe_eq_pi , Real.volume_pi_Ioc_to_real box.lower_le_upper _ ]
                  refine' prod_le_one fun _ _ => sub_nonneg . 2 $ box.lower_le_upper _ _ fun j hj => _
                  calc
                    J.upper i.succ_above j - J.lower i.succ_above j ≤ dist J.upper i.succ_above j J.lower i.succ_above j
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
              rcases nhds_within_has_basis nhds_basis_closed_ball _ . mem_iff . 1 Hd x hx . def ε'0 with ⟨ δ , δ0 , Hδ ⟩
              refine' ⟨ δ , δ0 , fun J hle hJδ hxJ hJc => _ ⟩
              simp only [ box_additive_map.volume_apply , box.volume_apply , dist_eq_norm ]
              refine'
                norm_volume_sub_integral_face_upper_sub_lower_smul_le
                      _ Hc.mono $ box.le_iff_Icc . 1 hle hxJ ε'0 fun y hy => Hδ _ hJc rfl
                    .
                    trans
                  _
              · exact ⟨ hJδ hy , box.le_iff_Icc . 1 hle hy ⟩
              ·
                rw [ mul_right_commₓ ( 2 : ℝ ) , ← box.volume_apply ]
                  exact mul_le_mul_of_nonneg_right hlt.le Ennreal.to_real_nonneg

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
 (Command.declModifiers
  [(Command.docComment
    "/--"
    " Divergence theorem for a Henstock-Kurzweil style integral.\n\nIf `f : ℝⁿ⁺¹ → Eⁿ⁺¹` is differentiable on a closed rectangular box `I` with derivative `f'`, then\nthe divergence `∑ i, f' x (pi.single i 1) i` is Henstock-Kurzweil integrable with integral equal to\nthe sum of integrals of `f` over the faces of `I` taken with appropriate signs.\n\nMore precisely, we use a non-standard generalization of the Henstock-Kurzweil integral and\nwe allow `f` to be non-differentiable (but still continuous) at a countable set of points. -/")]
  []
  []
  []
  []
  [])
 (Command.theorem
  "theorem"
  (Command.declId `has_integral_bot_divergence_of_forall_has_deriv_within_at [])
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
       (Topology.Algebra.Module.«term_→L[_]_»
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
     [":" (Term.app `Set [(BoxIntegral.Analysis.BoxIntegral.DivergenceTheorem.«termℝⁿ⁺¹» "ℝⁿ⁺¹")])]
     []
     ")")
    (Term.explicitBinder "(" [`hs] [":" (Term.app `countable [`s])] [] ")")
    (Term.explicitBinder
     "("
     [`Hs]
     [":"
      (Term.forall
       "∀"
       []
       ","
       (Mathlib.ExtendedBinder.«term∀___,_»
        "∀"
        `x
        («binderTerm∈_» "∈" `s)
        ","
        (Term.forall "∀" [] "," (Term.app `ContinuousWithinAt [`f `I.Icc `x]))))]
     []
     ")")
    (Term.explicitBinder
     "("
     [`Hd]
     [":"
      (Term.forall
       "∀"
       []
       ","
       (Mathlib.ExtendedBinder.«term∀___,_»
        "∀"
        `x
        («binderTerm∈_» "∈" (Init.Core.«term_\_» `I.Icc " \\ " `s))
        ","
        (Term.forall "∀" [] "," (Term.app `HasFderivWithinAt [`f (Term.app `f' [`x]) `I.Icc `x]))))]
     []
     ")")]
   (Term.typeSpec
    ":"
    (Term.app
     (Term.explicitUniv `has_integral ".{" [(numLit "0") "," `u "," `u] "}")
     [`I
      (Order.BoundedOrder.«term⊥» "⊥")
      (Term.fun
       "fun"
       (Term.basicFun
        [(Term.simpleBinder [`x] [])]
        "=>"
        (Algebra.BigOperators.Basic.«term∑_,_»
         "∑"
         (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `i)] []))
         ", "
         (Term.app `f' [`x (Term.app `Pi.single [`i (numLit "1")]) `i]))))
      `box_additive_map.volume
      (Algebra.BigOperators.Basic.«term∑_,_»
       "∑"
       (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `i)] []))
       ", "
       («term_-_»
        (Term.app
         (Term.explicitUniv `integral ".{" [(numLit "0") "," `u "," `u] "}")
         [(Term.app `I.face [`i])
          (Order.BoundedOrder.«term⊥» "⊥")
          (Term.fun
           "fun"
           (Term.basicFun
            [(Term.simpleBinder [`x] [])]
            "=>"
            (Term.app `f [(Term.app `i.insert_nth [(Term.app `I.upper [`i]) `x]) `i])))
          `box_additive_map.volume])
        "-"
        (Term.app
         (Term.explicitUniv `integral ".{" [(numLit "0") "," `u "," `u] "}")
         [(Term.app `I.face [`i])
          (Order.BoundedOrder.«term⊥» "⊥")
          (Term.fun
           "fun"
           (Term.basicFun
            [(Term.simpleBinder [`x] [])]
            "=>"
            (Term.app `f [(Term.app `i.insert_nth [(Term.app `I.lower [`i]) `x]) `i])))
          `box_additive_map.volume])))])))
  (Command.declValSimple
   ":="
   (Term.byTactic
    "by"
    (Tactic.tacticSeq
     (Tactic.tacticSeq1Indented
      [(group
        (Tactic.refine'
         "refine'"
         (Term.app
          `has_integral_sum
          [(Term.fun "fun" (Term.basicFun [(Term.simpleBinder [`i `hi] [])] "=>" (Term.hole "_")))]))
        [])
       (group (Tactic.clear "clear" [`hi]) [])
       (group
        (Tactic.simp
         "simp"
         []
         ["only"]
         ["["
          [(Tactic.simpLemma [] [] `has_fderiv_within_at_pi') "," (Tactic.simpLemma [] [] `continuous_within_at_pi)]
          "]"]
         [(Tactic.location "at" (Tactic.locationHyp [`Hd `Hs] []))])
        [])
       (group
        (Tactic.convert
         "convert"
         []
         (Term.app
          `has_integral_bot_pderiv
          [`I
           (Term.hole "_")
           (Term.hole "_")
           `s
           `hs
           (Term.fun "fun" (Term.basicFun [(Term.simpleBinder [`x `hx] [])] "=>" (Term.app `Hs [`x `hx `i])))
           (Term.fun "fun" (Term.basicFun [(Term.simpleBinder [`x `hx] [])] "=>" (Term.app `Hd [`x `hx `i])))
           `i])
         [])
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
       (Tactic.refine'
        "refine'"
        (Term.app
         `has_integral_sum
         [(Term.fun "fun" (Term.basicFun [(Term.simpleBinder [`i `hi] [])] "=>" (Term.hole "_")))]))
       [])
      (group (Tactic.clear "clear" [`hi]) [])
      (group
       (Tactic.simp
        "simp"
        []
        ["only"]
        ["["
         [(Tactic.simpLemma [] [] `has_fderiv_within_at_pi') "," (Tactic.simpLemma [] [] `continuous_within_at_pi)]
         "]"]
        [(Tactic.location "at" (Tactic.locationHyp [`Hd `Hs] []))])
       [])
      (group
       (Tactic.convert
        "convert"
        []
        (Term.app
         `has_integral_bot_pderiv
         [`I
          (Term.hole "_")
          (Term.hole "_")
          `s
          `hs
          (Term.fun "fun" (Term.basicFun [(Term.simpleBinder [`x `hx] [])] "=>" (Term.app `Hs [`x `hx `i])))
          (Term.fun "fun" (Term.basicFun [(Term.simpleBinder [`x `hx] [])] "=>" (Term.app `Hd [`x `hx `i])))
          `i])
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
  (Tactic.convert
   "convert"
   []
   (Term.app
    `has_integral_bot_pderiv
    [`I
     (Term.hole "_")
     (Term.hole "_")
     `s
     `hs
     (Term.fun "fun" (Term.basicFun [(Term.simpleBinder [`x `hx] [])] "=>" (Term.app `Hs [`x `hx `i])))
     (Term.fun "fun" (Term.basicFun [(Term.simpleBinder [`x `hx] [])] "=>" (Term.app `Hd [`x `hx `i])))
     `i])
   [])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.convert', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.app
   `has_integral_bot_pderiv
   [`I
    (Term.hole "_")
    (Term.hole "_")
    `s
    `hs
    (Term.fun "fun" (Term.basicFun [(Term.simpleBinder [`x `hx] [])] "=>" (Term.app `Hs [`x `hx `i])))
    (Term.fun "fun" (Term.basicFun [(Term.simpleBinder [`x `hx] [])] "=>" (Term.app `Hd [`x `hx `i])))
    `i])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `i
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
  (Term.fun "fun" (Term.basicFun [(Term.simpleBinder [`x `hx] [])] "=>" (Term.app `Hd [`x `hx `i])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.fun.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.basicFun', expected 'Lean.Parser.Term.basicFun.antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.app `Hd [`x `hx `i])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `i
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
  `hx
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
  `x
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `Hd
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
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (some 0, term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
 "("
 [(Term.fun "fun" (Term.basicFun [(Term.simpleBinder [`x `hx] [])] "=>" (Term.app `Hd [`x `hx `i]))) []]
 ")")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
  (Term.fun "fun" (Term.basicFun [(Term.simpleBinder [`x `hx] [])] "=>" (Term.app `Hs [`x `hx `i])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.fun.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.basicFun', expected 'Lean.Parser.Term.basicFun.antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.app `Hs [`x `hx `i])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `i
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
  `hx
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
  `x
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `Hs
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
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (some 0, term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
 "("
 [(Term.fun "fun" (Term.basicFun [(Term.simpleBinder [`x `hx] [])] "=>" (Term.app `Hs [`x `hx `i]))) []]
 ")")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
  `hs
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
  `s
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (some 1024, term)
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
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, term))
  `I
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (some 1023, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `has_integral_bot_pderiv
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'group', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, tactic))
  (Tactic.simp
   "simp"
   []
   ["only"]
   ["[" [(Tactic.simpLemma [] [] `has_fderiv_within_at_pi') "," (Tactic.simpLemma [] [] `continuous_within_at_pi)] "]"]
   [(Tactic.location "at" (Tactic.locationHyp [`Hd `Hs] []))])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simp', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.location', expected 'optional.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.locationHyp', expected 'Lean.Parser.Tactic.locationWildcard'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `Hs
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
  `Hd
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«]»', expected 'optional.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `continuous_within_at_pi
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `has_fderiv_within_at_pi'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'only', expected 'optional.antiquot_scope'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'group', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, tactic))
  (Tactic.clear "clear" [`hi])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.clear', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `hi
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'group', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, tactic))
  (Tactic.refine'
   "refine'"
   (Term.app
    `has_integral_sum
    [(Term.fun "fun" (Term.basicFun [(Term.simpleBinder [`i `hi] [])] "=>" (Term.hole "_")))]))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.refine'', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.app `has_integral_sum [(Term.fun "fun" (Term.basicFun [(Term.simpleBinder [`i `hi] [])] "=>" (Term.hole "_")))])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.fun "fun" (Term.basicFun [(Term.simpleBinder [`i `hi] [])] "=>" (Term.hole "_")))
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
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `has_integral_sum
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, tactic) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.declSig', expected 'Lean.Parser.Command.declSig.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.typeSpec', expected 'Lean.Parser.Term.typeSpec.antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
  (Term.app
   (Term.explicitUniv `has_integral ".{" [(numLit "0") "," `u "," `u] "}")
   [`I
    (Order.BoundedOrder.«term⊥» "⊥")
    (Term.fun
     "fun"
     (Term.basicFun
      [(Term.simpleBinder [`x] [])]
      "=>"
      (Algebra.BigOperators.Basic.«term∑_,_»
       "∑"
       (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `i)] []))
       ", "
       (Term.app `f' [`x (Term.app `Pi.single [`i (numLit "1")]) `i]))))
    `box_additive_map.volume
    (Algebra.BigOperators.Basic.«term∑_,_»
     "∑"
     (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `i)] []))
     ", "
     («term_-_»
      (Term.app
       (Term.explicitUniv `integral ".{" [(numLit "0") "," `u "," `u] "}")
       [(Term.app `I.face [`i])
        (Order.BoundedOrder.«term⊥» "⊥")
        (Term.fun
         "fun"
         (Term.basicFun
          [(Term.simpleBinder [`x] [])]
          "=>"
          (Term.app `f [(Term.app `i.insert_nth [(Term.app `I.upper [`i]) `x]) `i])))
        `box_additive_map.volume])
      "-"
      (Term.app
       (Term.explicitUniv `integral ".{" [(numLit "0") "," `u "," `u] "}")
       [(Term.app `I.face [`i])
        (Order.BoundedOrder.«term⊥» "⊥")
        (Term.fun
         "fun"
         (Term.basicFun
          [(Term.simpleBinder [`x] [])]
          "=>"
          (Term.app `f [(Term.app `i.insert_nth [(Term.app `I.lower [`i]) `x]) `i])))
        `box_additive_map.volume])))])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Algebra.BigOperators.Basic.«term∑_,_»', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Algebra.BigOperators.Basic.«term∑_,_»', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Algebra.BigOperators.Basic.«term∑_,_»', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Algebra.BigOperators.Basic.«term∑_,_»', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Algebra.BigOperators.Basic.«term∑_,_»', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Algebra.BigOperators.Basic.«term∑_,_»
   "∑"
   (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `i)] []))
   ", "
   («term_-_»
    (Term.app
     (Term.explicitUniv `integral ".{" [(numLit "0") "," `u "," `u] "}")
     [(Term.app `I.face [`i])
      (Order.BoundedOrder.«term⊥» "⊥")
      (Term.fun
       "fun"
       (Term.basicFun
        [(Term.simpleBinder [`x] [])]
        "=>"
        (Term.app `f [(Term.app `i.insert_nth [(Term.app `I.upper [`i]) `x]) `i])))
      `box_additive_map.volume])
    "-"
    (Term.app
     (Term.explicitUniv `integral ".{" [(numLit "0") "," `u "," `u] "}")
     [(Term.app `I.face [`i])
      (Order.BoundedOrder.«term⊥» "⊥")
      (Term.fun
       "fun"
       (Term.basicFun
        [(Term.simpleBinder [`x] [])]
        "=>"
        (Term.app `f [(Term.app `i.insert_nth [(Term.app `I.lower [`i]) `x]) `i])))
      `box_additive_map.volume])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Algebra.BigOperators.Basic.«term∑_,_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  («term_-_»
   (Term.app
    (Term.explicitUniv `integral ".{" [(numLit "0") "," `u "," `u] "}")
    [(Term.app `I.face [`i])
     (Order.BoundedOrder.«term⊥» "⊥")
     (Term.fun
      "fun"
      (Term.basicFun
       [(Term.simpleBinder [`x] [])]
       "=>"
       (Term.app `f [(Term.app `i.insert_nth [(Term.app `I.upper [`i]) `x]) `i])))
     `box_additive_map.volume])
   "-"
   (Term.app
    (Term.explicitUniv `integral ".{" [(numLit "0") "," `u "," `u] "}")
    [(Term.app `I.face [`i])
     (Order.BoundedOrder.«term⊥» "⊥")
     (Term.fun
      "fun"
      (Term.basicFun
       [(Term.simpleBinder [`x] [])]
       "=>"
       (Term.app `f [(Term.app `i.insert_nth [(Term.app `I.lower [`i]) `x]) `i])))
     `box_additive_map.volume]))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_-_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.app
   (Term.explicitUniv `integral ".{" [(numLit "0") "," `u "," `u] "}")
   [(Term.app `I.face [`i])
    (Order.BoundedOrder.«term⊥» "⊥")
    (Term.fun
     "fun"
     (Term.basicFun
      [(Term.simpleBinder [`x] [])]
      "=>"
      (Term.app `f [(Term.app `i.insert_nth [(Term.app `I.lower [`i]) `x]) `i])))
    `box_additive_map.volume])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `box_additive_map.volume
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
  (Term.fun
   "fun"
   (Term.basicFun
    [(Term.simpleBinder [`x] [])]
    "=>"
    (Term.app `f [(Term.app `i.insert_nth [(Term.app `I.lower [`i]) `x]) `i])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.fun.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.basicFun', expected 'Lean.Parser.Term.basicFun.antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.app `f [(Term.app `i.insert_nth [(Term.app `I.lower [`i]) `x]) `i])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `i
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
  (Term.app `i.insert_nth [(Term.app `I.lower [`i]) `x])
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
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
  (Term.app `I.lower [`i])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `i
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `I.lower
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023, term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren "(" [(Term.app `I.lower [`i]) []] ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `i.insert_nth
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023, term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
 "("
 [(Term.app `i.insert_nth [(Term.paren "(" [(Term.app `I.lower [`i]) []] ")") `x]) []]
 ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `f
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
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (some 0, term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
 "("
 [(Term.fun
   "fun"
   (Term.basicFun
    [(Term.simpleBinder [`x] [])]
    "=>"
    (Term.app
     `f
     [(Term.paren "(" [(Term.app `i.insert_nth [(Term.paren "(" [(Term.app `I.lower [`i]) []] ")") `x]) []] ")") `i])))
  []]
 ")")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Order.BoundedOrder.«term⊥»', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Order.BoundedOrder.«term⊥»', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Order.BoundedOrder.«term⊥»', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Order.BoundedOrder.«term⊥»', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Order.BoundedOrder.«term⊥»', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
  (Order.BoundedOrder.«term⊥» "⊥")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Order.BoundedOrder.«term⊥»', expected 'antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, term))
  (Term.app `I.face [`i])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `i
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `I.face
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023, term) <=? (some 1023, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren "(" [(Term.app `I.face [`i]) []] ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  (Term.explicitUniv `integral ".{" [(numLit "0") "," `u "," `u] "}")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.explicitUniv', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `u
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `u
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'numLit', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (numLit "0")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'numLit', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'numLit', expected 'numLit.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
  `integral
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 66 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 65, term))
  (Term.app
   (Term.explicitUniv `integral ".{" [(numLit "0") "," `u "," `u] "}")
   [(Term.app `I.face [`i])
    (Order.BoundedOrder.«term⊥» "⊥")
    (Term.fun
     "fun"
     (Term.basicFun
      [(Term.simpleBinder [`x] [])]
      "=>"
      (Term.app `f [(Term.app `i.insert_nth [(Term.app `I.upper [`i]) `x]) `i])))
    `box_additive_map.volume])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `box_additive_map.volume
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
  (Term.fun
   "fun"
   (Term.basicFun
    [(Term.simpleBinder [`x] [])]
    "=>"
    (Term.app `f [(Term.app `i.insert_nth [(Term.app `I.upper [`i]) `x]) `i])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.fun.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.basicFun', expected 'Lean.Parser.Term.basicFun.antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.app `f [(Term.app `i.insert_nth [(Term.app `I.upper [`i]) `x]) `i])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `i
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
  (Term.app `i.insert_nth [(Term.app `I.upper [`i]) `x])
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
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
  (Term.app `I.upper [`i])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `i
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `I.upper
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023, term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren "(" [(Term.app `I.upper [`i]) []] ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `i.insert_nth
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023, term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
 "("
 [(Term.app `i.insert_nth [(Term.paren "(" [(Term.app `I.upper [`i]) []] ")") `x]) []]
 ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `f
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
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (some 0, term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
 "("
 [(Term.fun
   "fun"
   (Term.basicFun
    [(Term.simpleBinder [`x] [])]
    "=>"
    (Term.app
     `f
     [(Term.paren "(" [(Term.app `i.insert_nth [(Term.paren "(" [(Term.app `I.upper [`i]) []] ")") `x]) []] ")") `i])))
  []]
 ")")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Order.BoundedOrder.«term⊥»', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Order.BoundedOrder.«term⊥»', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Order.BoundedOrder.«term⊥»', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Order.BoundedOrder.«term⊥»', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Order.BoundedOrder.«term⊥»', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
  (Order.BoundedOrder.«term⊥» "⊥")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Order.BoundedOrder.«term⊥»', expected 'antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, term))
  (Term.app `I.face [`i])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `i
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `I.face
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023, term) <=? (some 1023, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren "(" [(Term.app `I.face [`i]) []] ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  (Term.explicitUniv `integral ".{" [(numLit "0") "," `u "," `u] "}")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.explicitUniv', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `u
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `u
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'numLit', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (numLit "0")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'numLit', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'numLit', expected 'numLit.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
  `integral
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 65 >? 1022, (some 1023, term) <=? (some 65, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 65, (some 66, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.explicitBinders', expected 'Mathlib.ExtendedBinder.extBinders'
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
    Divergence theorem for a Henstock-Kurzweil style integral.
    
    If `f : ℝⁿ⁺¹ → Eⁿ⁺¹` is differentiable on a closed rectangular box `I` with derivative `f'`, then
    the divergence `∑ i, f' x (pi.single i 1) i` is Henstock-Kurzweil integrable with integral equal to
    the sum of integrals of `f` over the faces of `I` taken with appropriate signs.
    
    More precisely, we use a non-standard generalization of the Henstock-Kurzweil integral and
    we allow `f` to be non-differentiable (but still continuous) at a countable set of points. -/
  theorem
    has_integral_bot_divergence_of_forall_has_deriv_within_at
    ( f : ℝⁿ⁺¹ → Eⁿ⁺¹ )
        ( f' : ℝⁿ⁺¹ → ℝⁿ⁺¹ →L[ ℝ ] Eⁿ⁺¹ )
        ( s : Set ℝⁿ⁺¹ )
        ( hs : countable s )
        ( Hs : ∀ , ∀ x ∈ s , ∀ , ContinuousWithinAt f I.Icc x )
        ( Hd : ∀ , ∀ x ∈ I.Icc \ s , ∀ , HasFderivWithinAt f f' x I.Icc x )
      :
        has_integral .{ 0 , u , u }
          I
            ⊥
            fun x => ∑ i , f' x Pi.single i 1 i
            box_additive_map.volume
            ∑
              i
              ,
              integral .{ 0 , u , u } I.face i ⊥ fun x => f i.insert_nth I.upper i x i box_additive_map.volume
                -
                integral .{ 0 , u , u } I.face i ⊥ fun x => f i.insert_nth I.lower i x i box_additive_map.volume
    :=
      by
        refine' has_integral_sum fun i hi => _
          clear hi
          simp only [ has_fderiv_within_at_pi' , continuous_within_at_pi ] at Hd Hs
          convert has_integral_bot_pderiv I _ _ s hs fun x hx => Hs x hx i fun x hx => Hd x hx i i

end BoxIntegral

