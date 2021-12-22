import Mathbin.Analysis.NormedSpace.Exponential
import Mathbin.Analysis.Calculus.FderivAnalytic
import Mathbin.Data.Complex.Exponential
import Mathbin.Topology.MetricSpace.CauSeqFilter

/-!
# Calculus results on exponential in a Banach algebra

In this file, we prove basic properties about the derivative of the exponential map `exp 𝕂 𝔸`
in a Banach algebra `𝔸` over a field `𝕂`. We keep them separate from the main file
`analysis/normed_space/exponential` in order to minimize dependencies.

## Main results

We prove most result for an arbitrary field `𝕂`, and then specialize to `𝕂 = ℝ` or `𝕂 = ℂ`.

### General case

- `has_strict_fderiv_at_exp_zero_of_radius_pos` : `exp 𝕂 𝔸` has strict Fréchet-derivative
  `1 : 𝔸 →L[𝕂] 𝔸` at zero, as long as it converges on a neighborhood of zero
  (see also `has_strict_deriv_at_exp_zero_of_radius_pos` for the case `𝔸 = 𝕂`)
- `has_strict_fderiv_at_exp_of_lt_radius` : if `𝕂` has characteristic zero and `𝔸` is commutative,
  then given a point `x` in the disk of convergence, `exp 𝕂 𝔸` as strict Fréchet-derivative
  `exp 𝕂 𝔸 x • 1 : 𝔸 →L[𝕂] 𝔸` at x (see also `has_strict_deriv_at_exp_of_lt_radius` for the case
  `𝔸 = 𝕂`)

### `𝕂 = ℝ` or `𝕂 = ℂ`

- `has_strict_fderiv_at_exp_zero` : `exp 𝕂 𝔸` has strict Fréchet-derivative `1 : 𝔸 →L[𝕂] 𝔸` at zero
  (see also `has_strict_deriv_at_exp_zero` for the case `𝔸 = 𝕂`)
- `has_strict_fderiv_at_exp` : if `𝔸` is commutative, then given any point `x`, `exp 𝕂 𝔸` as strict
  Fréchet-derivative `exp 𝕂 𝔸 x • 1 : 𝔸 →L[𝕂] 𝔸` at x (see also `has_strict_deriv_at_exp` for the
  case `𝔸 = 𝕂`)

### Compatibilty with `real.exp` and `complex.exp`

- `complex.exp_eq_exp_ℂ_ℂ` : `complex.exp = exp ℂ ℂ`
- `real.exp_eq_exp_ℝ_ℝ` : `real.exp = exp ℝ ℝ`

-/


open Filter IsROrC ContinuousMultilinearMap NormedField Asymptotics

open_locale Nat TopologicalSpace BigOperators Ennreal

section AnyFieldAnyAlgebra

variable {𝕂 𝔸 : Type _} [NondiscreteNormedField 𝕂] [NormedRing 𝔸] [NormedAlgebra 𝕂 𝔸] [CompleteSpace 𝔸]

/--  The exponential in a Banach-algebra `𝔸` over a normed field `𝕂` has strict Fréchet-derivative
`1 : 𝔸 →L[𝕂] 𝔸` at zero, as long as it converges on a neighborhood of zero. -/
theorem has_strict_fderiv_at_exp_zero_of_radius_pos (h : 0 < (expSeries 𝕂 𝔸).radius) :
    HasStrictFderivAt (exp 𝕂 𝔸) (1 : 𝔸 →L[𝕂] 𝔸) 0 := by
  convert (has_fpower_series_at_exp_zero_of_radius_pos h).HasStrictFderivAt
  ext x
  change x = expSeries 𝕂 𝔸 1 fun _ => x
  simp [exp_series_apply_eq]

/--  The exponential in a Banach-algebra `𝔸` over a normed field `𝕂` has Fréchet-derivative
`1 : 𝔸 →L[𝕂] 𝔸` at zero, as long as it converges on a neighborhood of zero. -/
theorem has_fderiv_at_exp_zero_of_radius_pos (h : 0 < (expSeries 𝕂 𝔸).radius) :
    HasFderivAt (exp 𝕂 𝔸) (1 : 𝔸 →L[𝕂] 𝔸) 0 :=
  (has_strict_fderiv_at_exp_zero_of_radius_pos h).HasFderivAt

end AnyFieldAnyAlgebra

section AnyFieldCommAlgebra

variable {𝕂 𝔸 : Type _} [NondiscreteNormedField 𝕂] [NormedCommRing 𝔸] [NormedAlgebra 𝕂 𝔸] [CompleteSpace 𝔸]

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
 (Command.declModifiers
  [(Command.docComment
    "/--"
    " The exponential map in a commutative Banach-algebra `𝔸` over a normed field `𝕂` of\ncharacteristic zero has Fréchet-derivative `exp 𝕂 𝔸 x • 1 : 𝔸 →L[𝕂] 𝔸` at any point `x` in the\ndisk of convergence. -/")]
  []
  []
  []
  []
  [])
 (Command.theorem
  "theorem"
  (Command.declId `has_fderiv_at_exp_of_mem_ball [])
  (Command.declSig
   [(Term.instBinder "[" [] (Term.app `CharZero [`𝕂]) "]")
    (Term.implicitBinder "{" [`x] [":" `𝔸] "}")
    (Term.explicitBinder
     "("
     [`hx]
     [":"
      (Init.Core.«term_∈_»
       `x
       " ∈ "
       (Term.app
        `Emetric.Ball
        [(Term.paren "(" [(numLit "0") [(Term.typeAscription ":" `𝔸)]] ")")
         (Term.proj (Term.app `expSeries [`𝕂 `𝔸]) "." `radius)]))]
     []
     ")")]
   (Term.typeSpec
    ":"
    (Term.app
     `HasFderivAt
     [(Term.app `exp [`𝕂 `𝔸])
      (Term.paren
       "("
       [(Algebra.Group.Defs.«term_•_» (Term.app `exp [`𝕂 `𝔸 `x]) " • " (numLit "1"))
        [(Term.typeAscription ":" (Topology.Algebra.Module.«term_→L[_]_» `𝔸 " →L[" `𝕂 "] " `𝔸))]]
       ")")
      `x])))
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
           [`hpos []]
           [(Term.typeSpec ":" («term_<_» (numLit "0") "<" (Term.proj (Term.app `expSeries [`𝕂 `𝔸]) "." `radius)))]
           ":="
           (Term.app (Term.proj (Term.app `zero_le [(Term.hole "_")]) "." `trans_lt) [`hx]))))
        [])
       (group
        (Tactic.rwSeq "rw" [] (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `has_fderiv_at_iff_is_o_nhds_zero)] "]") [])
        [])
       (group
        (Tactic.tacticSuffices_
         "suffices"
         (Term.sufficesDecl
          []
          (Filter.Order.Filter.Basic.«term_=ᶠ[_]_»
           (Term.fun
            "fun"
            (Term.basicFun
             [(Term.simpleBinder [`h] [])]
             "=>"
             (Finset.Data.Finset.Fold.«term_*_»
              (Term.app `exp [`𝕂 `𝔸 `x])
              "*"
              («term_-_»
               («term_-_»
                (Term.app `exp [`𝕂 `𝔸 (Init.Logic.«term_+_» (numLit "0") "+" `h)])
                "-"
                (Term.app `exp [`𝕂 `𝔸 (numLit "0")]))
               "-"
               (Term.app `ContinuousLinearMap.id [`𝕂 `𝔸 `h])))))
           " =ᶠ["
           (Term.app (Topology.Basic.term𝓝 "𝓝") [(numLit "0")])
           "] "
           (Term.fun
            "fun"
            (Term.basicFun
             [(Term.simpleBinder [`h] [])]
             "=>"
             («term_-_»
              («term_-_» (Term.app `exp [`𝕂 `𝔸 (Init.Logic.«term_+_» `x "+" `h)]) "-" (Term.app `exp [`𝕂 `𝔸 `x]))
              "-"
              (Algebra.Group.Defs.«term_•_»
               (Term.app `exp [`𝕂 `𝔸 `x])
               " • "
               (Term.app `ContinuousLinearMap.id [`𝕂 `𝔸 `h]))))))
          (Term.byTactic
           "by"
           (Tactic.tacticSeq
            (Tactic.tacticSeq1Indented
             [(group
               (Tactic.refine'
                "refine'"
                (Term.app
                 (Term.proj (Term.app `is_o.const_mul_left [(Term.hole "_") (Term.hole "_")]) "." `congr')
                 [`this (Term.app `eventually_eq.refl [(Term.hole "_") (Term.hole "_")])]))
               [])
              (group
               (Tactic.rwSeq
                "rw"
                []
                (Tactic.rwRuleSeq "[" [(Tactic.rwRule ["←"] `has_fderiv_at_iff_is_o_nhds_zero)] "]")
                [])
               [])
              (group (Tactic.exact "exact" (Term.app `has_fderiv_at_exp_zero_of_radius_pos [`hpos])) [])])))))
        [])
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
              (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `h)] []))
              " in "
              (Term.app (Topology.Basic.term𝓝 "𝓝") [(Term.paren "(" [(numLit "0") [(Term.typeAscription ":" `𝔸)]] ")")])
              ", "
              (Init.Core.«term_∈_»
               `h
               " ∈ "
               (Term.app
                `Emetric.Ball
                [(Term.paren "(" [(numLit "0") [(Term.typeAscription ":" `𝔸)]] ")")
                 (Term.proj (Term.app `expSeries [`𝕂 `𝔸]) "." `radius)]))))]
           ":="
           (Term.app `Emetric.ball_mem_nhds [(Term.hole "_") `hpos]))))
        [])
       (group (Tactic.filterUpwards "filter_upwards" "[" [`this] "]" []) [])
       (group (Tactic.intro "intro" [`h `hh]) [])
       (group
        (Tactic.rwSeq
         "rw"
         []
         (Tactic.rwRuleSeq
          "["
          [(Tactic.rwRule [] (Term.app `exp_add_of_mem_ball [`hx `hh]))
           ","
           (Tactic.rwRule [] `exp_zero)
           ","
           (Tactic.rwRule [] `zero_addₓ)
           ","
           (Tactic.rwRule [] `ContinuousLinearMap.id_apply)
           ","
           (Tactic.rwRule [] `smul_eq_mul)]
          "]")
         [])
        [])
       (group (Tactic.Ring.tacticRing "ring") [])])))
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
          [`hpos []]
          [(Term.typeSpec ":" («term_<_» (numLit "0") "<" (Term.proj (Term.app `expSeries [`𝕂 `𝔸]) "." `radius)))]
          ":="
          (Term.app (Term.proj (Term.app `zero_le [(Term.hole "_")]) "." `trans_lt) [`hx]))))
       [])
      (group
       (Tactic.rwSeq "rw" [] (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `has_fderiv_at_iff_is_o_nhds_zero)] "]") [])
       [])
      (group
       (Tactic.tacticSuffices_
        "suffices"
        (Term.sufficesDecl
         []
         (Filter.Order.Filter.Basic.«term_=ᶠ[_]_»
          (Term.fun
           "fun"
           (Term.basicFun
            [(Term.simpleBinder [`h] [])]
            "=>"
            (Finset.Data.Finset.Fold.«term_*_»
             (Term.app `exp [`𝕂 `𝔸 `x])
             "*"
             («term_-_»
              («term_-_»
               (Term.app `exp [`𝕂 `𝔸 (Init.Logic.«term_+_» (numLit "0") "+" `h)])
               "-"
               (Term.app `exp [`𝕂 `𝔸 (numLit "0")]))
              "-"
              (Term.app `ContinuousLinearMap.id [`𝕂 `𝔸 `h])))))
          " =ᶠ["
          (Term.app (Topology.Basic.term𝓝 "𝓝") [(numLit "0")])
          "] "
          (Term.fun
           "fun"
           (Term.basicFun
            [(Term.simpleBinder [`h] [])]
            "=>"
            («term_-_»
             («term_-_» (Term.app `exp [`𝕂 `𝔸 (Init.Logic.«term_+_» `x "+" `h)]) "-" (Term.app `exp [`𝕂 `𝔸 `x]))
             "-"
             (Algebra.Group.Defs.«term_•_»
              (Term.app `exp [`𝕂 `𝔸 `x])
              " • "
              (Term.app `ContinuousLinearMap.id [`𝕂 `𝔸 `h]))))))
         (Term.byTactic
          "by"
          (Tactic.tacticSeq
           (Tactic.tacticSeq1Indented
            [(group
              (Tactic.refine'
               "refine'"
               (Term.app
                (Term.proj (Term.app `is_o.const_mul_left [(Term.hole "_") (Term.hole "_")]) "." `congr')
                [`this (Term.app `eventually_eq.refl [(Term.hole "_") (Term.hole "_")])]))
              [])
             (group
              (Tactic.rwSeq
               "rw"
               []
               (Tactic.rwRuleSeq "[" [(Tactic.rwRule ["←"] `has_fderiv_at_iff_is_o_nhds_zero)] "]")
               [])
              [])
             (group (Tactic.exact "exact" (Term.app `has_fderiv_at_exp_zero_of_radius_pos [`hpos])) [])])))))
       [])
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
             (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `h)] []))
             " in "
             (Term.app (Topology.Basic.term𝓝 "𝓝") [(Term.paren "(" [(numLit "0") [(Term.typeAscription ":" `𝔸)]] ")")])
             ", "
             (Init.Core.«term_∈_»
              `h
              " ∈ "
              (Term.app
               `Emetric.Ball
               [(Term.paren "(" [(numLit "0") [(Term.typeAscription ":" `𝔸)]] ")")
                (Term.proj (Term.app `expSeries [`𝕂 `𝔸]) "." `radius)]))))]
          ":="
          (Term.app `Emetric.ball_mem_nhds [(Term.hole "_") `hpos]))))
       [])
      (group (Tactic.filterUpwards "filter_upwards" "[" [`this] "]" []) [])
      (group (Tactic.intro "intro" [`h `hh]) [])
      (group
       (Tactic.rwSeq
        "rw"
        []
        (Tactic.rwRuleSeq
         "["
         [(Tactic.rwRule [] (Term.app `exp_add_of_mem_ball [`hx `hh]))
          ","
          (Tactic.rwRule [] `exp_zero)
          ","
          (Tactic.rwRule [] `zero_addₓ)
          ","
          (Tactic.rwRule [] `ContinuousLinearMap.id_apply)
          ","
          (Tactic.rwRule [] `smul_eq_mul)]
         "]")
        [])
       [])
      (group (Tactic.Ring.tacticRing "ring") [])])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.byTactic', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.byTactic', expected 'Lean.Parser.Term.byTactic.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq', expected 'Lean.Parser.Tactic.tacticSeq.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeq1Indented.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'group', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Tactic.Ring.tacticRing "ring")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Tactic.Ring.tacticRing', expected 'antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'group', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, tactic))
  (Tactic.rwSeq
   "rw"
   []
   (Tactic.rwRuleSeq
    "["
    [(Tactic.rwRule [] (Term.app `exp_add_of_mem_ball [`hx `hh]))
     ","
     (Tactic.rwRule [] `exp_zero)
     ","
     (Tactic.rwRule [] `zero_addₓ)
     ","
     (Tactic.rwRule [] `ContinuousLinearMap.id_apply)
     ","
     (Tactic.rwRule [] `smul_eq_mul)]
    "]")
   [])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.rwSeq', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.rwRule', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `smul_eq_mul
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.rwRule', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `ContinuousLinearMap.id_apply
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.rwRule', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `zero_addₓ
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.rwRule', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `exp_zero
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.rwRule', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.app `exp_add_of_mem_ball [`hx `hh])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `hh
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
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `exp_add_of_mem_ball
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'group', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, tactic))
  (Tactic.intro "intro" [`h `hh])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.intro', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `hh
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
  `h
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'group', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, tactic))
  (Tactic.filterUpwards "filter_upwards" "[" [`this] "]" [])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.filterUpwards', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `this
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
     []
     [(Term.typeSpec
       ":"
       (Filter.Order.Filter.Basic.«term∀ᶠ_in_,_»
        "∀ᶠ"
        (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `h)] []))
        " in "
        (Term.app (Topology.Basic.term𝓝 "𝓝") [(Term.paren "(" [(numLit "0") [(Term.typeAscription ":" `𝔸)]] ")")])
        ", "
        (Init.Core.«term_∈_»
         `h
         " ∈ "
         (Term.app
          `Emetric.Ball
          [(Term.paren "(" [(numLit "0") [(Term.typeAscription ":" `𝔸)]] ")")
           (Term.proj (Term.app `expSeries [`𝕂 `𝔸]) "." `radius)]))))]
     ":="
     (Term.app `Emetric.ball_mem_nhds [(Term.hole "_") `hpos]))))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticHave_', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.haveDecl', expected 'Lean.Parser.Term.haveDecl.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.haveIdDecl', expected 'Lean.Parser.Term.haveIdDecl.antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.app `Emetric.ball_mem_nhds [(Term.hole "_") `hpos])
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
  `Emetric.ball_mem_nhds
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.typeSpec', expected 'optional.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.typeSpec', expected 'Lean.Parser.Term.typeSpec.antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Filter.Order.Filter.Basic.«term∀ᶠ_in_,_»
   "∀ᶠ"
   (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `h)] []))
   " in "
   (Term.app (Topology.Basic.term𝓝 "𝓝") [(Term.paren "(" [(numLit "0") [(Term.typeAscription ":" `𝔸)]] ")")])
   ", "
   (Init.Core.«term_∈_»
    `h
    " ∈ "
    (Term.app
     `Emetric.Ball
     [(Term.paren "(" [(numLit "0") [(Term.typeAscription ":" `𝔸)]] ")")
      (Term.proj (Term.app `expSeries [`𝕂 `𝔸]) "." `radius)])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Filter.Order.Filter.Basic.«term∀ᶠ_in_,_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Init.Core.«term_∈_»
   `h
   " ∈ "
   (Term.app
    `Emetric.Ball
    [(Term.paren "(" [(numLit "0") [(Term.typeAscription ":" `𝔸)]] ")")
     (Term.proj (Term.app `expSeries [`𝕂 `𝔸]) "." `radius)]))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Init.Core.«term_∈_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.app
   `Emetric.Ball
   [(Term.paren "(" [(numLit "0") [(Term.typeAscription ":" `𝔸)]] ")")
    (Term.proj (Term.app `expSeries [`𝕂 `𝔸]) "." `radius)])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.proj', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.proj', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.proj', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.proj', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.proj', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.proj (Term.app `expSeries [`𝕂 `𝔸]) "." `radius)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.proj', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
  (Term.app `expSeries [`𝕂 `𝔸])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `𝔸
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
  `𝕂
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `expSeries
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren "(" [(Term.app `expSeries [`𝕂 `𝔸]) []] ")")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.paren', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.paren', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.paren', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.paren', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.paren', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
  (Term.paren "(" [(numLit "0") [(Term.typeAscription ":" `𝔸)]] ")")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.paren', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.paren', expected 'Lean.Parser.Term.paren.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'null', expected 'optional.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.typeAscription', expected 'optional.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.typeAscription', expected 'Lean.Parser.Term.tupleTail.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.typeAscription', expected 'Lean.Parser.Term.tupleTail'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.typeAscription', expected 'Lean.Parser.Term.typeAscription.antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `𝔸
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
  (numLit "0")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'numLit', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'numLit', expected 'numLit.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1023, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `Emetric.Ball
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 50, term))
  `h
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 50 >? 1024, (none, [anonymous]) <=? (some 50, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 50, (some 51, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.app (Topology.Basic.term𝓝 "𝓝") [(Term.paren "(" [(numLit "0") [(Term.typeAscription ":" `𝔸)]] ")")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.paren', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.paren', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.paren', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.paren', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.paren', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.paren "(" [(numLit "0") [(Term.typeAscription ":" `𝔸)]] ")")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.paren', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.paren', expected 'Lean.Parser.Term.paren.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'null', expected 'optional.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.typeAscription', expected 'optional.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.typeAscription', expected 'Lean.Parser.Term.tupleTail.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.typeAscription', expected 'Lean.Parser.Term.tupleTail'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.typeAscription', expected 'Lean.Parser.Term.typeAscription.antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `𝔸
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
  (numLit "0")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'numLit', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'numLit', expected 'numLit.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1023, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  (Topology.Basic.term𝓝 "𝓝")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Topology.Basic.term𝓝', expected 'antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
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
/--
    The exponential map in a commutative Banach-algebra `𝔸` over a normed field `𝕂` of
    characteristic zero has Fréchet-derivative `exp 𝕂 𝔸 x • 1 : 𝔸 →L[𝕂] 𝔸` at any point `x` in the
    disk of convergence. -/
  theorem
    has_fderiv_at_exp_of_mem_ball
    [ CharZero 𝕂 ] { x : 𝔸 } ( hx : x ∈ Emetric.Ball ( 0 : 𝔸 ) expSeries 𝕂 𝔸 . radius )
      : HasFderivAt exp 𝕂 𝔸 ( exp 𝕂 𝔸 x • 1 : 𝔸 →L[ 𝕂 ] 𝔸 ) x
    :=
      by
        have hpos : 0 < expSeries 𝕂 𝔸 . radius := zero_le _ . trans_lt hx
          rw [ has_fderiv_at_iff_is_o_nhds_zero ]
          suffices
            fun h => exp 𝕂 𝔸 x * exp 𝕂 𝔸 0 + h - exp 𝕂 𝔸 0 - ContinuousLinearMap.id 𝕂 𝔸 h
                =ᶠ[
                𝓝 0
                ]
                fun h => exp 𝕂 𝔸 x + h - exp 𝕂 𝔸 x - exp 𝕂 𝔸 x • ContinuousLinearMap.id 𝕂 𝔸 h
              by
                refine' is_o.const_mul_left _ _ . congr' this eventually_eq.refl _ _
                  rw [ ← has_fderiv_at_iff_is_o_nhds_zero ]
                  exact has_fderiv_at_exp_zero_of_radius_pos hpos
          have : ∀ᶠ h in 𝓝 ( 0 : 𝔸 ) , h ∈ Emetric.Ball ( 0 : 𝔸 ) expSeries 𝕂 𝔸 . radius := Emetric.ball_mem_nhds _ hpos
          filter_upwards [ this ]
          intro h hh
          rw [ exp_add_of_mem_ball hx hh , exp_zero , zero_addₓ , ContinuousLinearMap.id_apply , smul_eq_mul ]
          ring

/--  The exponential map in a commutative Banach-algebra `𝔸` over a normed field `𝕂` of
characteristic zero has strict Fréchet-derivative `exp 𝕂 𝔸 x • 1 : 𝔸 →L[𝕂] 𝔸` at any point `x` in
the disk of convergence. -/
theorem has_strict_fderiv_at_exp_of_mem_ball [CharZero 𝕂] {x : 𝔸}
    (hx : x ∈ Emetric.Ball (0 : 𝔸) (expSeries 𝕂 𝔸).radius) :
    HasStrictFderivAt (exp 𝕂 𝔸) (exp 𝕂 𝔸 x • 1 : 𝔸 →L[𝕂] 𝔸) x :=
  let ⟨p, hp⟩ := analytic_at_exp_of_mem_ball x hx
  hp.has_fderiv_at.unique (has_fderiv_at_exp_of_mem_ball hx) ▸ hp.has_strict_fderiv_at

end AnyFieldCommAlgebra

section deriv

variable {𝕂 : Type _} [NondiscreteNormedField 𝕂] [CompleteSpace 𝕂]

/--  The exponential map in a complete normed field `𝕂` of characteristic zero has strict derivative
`exp 𝕂 𝕂 x` at any point `x` in the disk of convergence. -/
theorem has_strict_deriv_at_exp_of_mem_ball [CharZero 𝕂] {x : 𝕂}
    (hx : x ∈ Emetric.Ball (0 : 𝕂) (expSeries 𝕂 𝕂).radius) : HasStrictDerivAt (exp 𝕂 𝕂) (exp 𝕂 𝕂 x) x := by
  simpa using (has_strict_fderiv_at_exp_of_mem_ball hx).HasStrictDerivAt

/--  The exponential map in a complete normed field `𝕂` of characteristic zero has derivative
`exp 𝕂 𝕂 x` at any point `x` in the disk of convergence. -/
theorem has_deriv_at_exp_of_mem_ball [CharZero 𝕂] {x : 𝕂} (hx : x ∈ Emetric.Ball (0 : 𝕂) (expSeries 𝕂 𝕂).radius) :
    HasDerivAt (exp 𝕂 𝕂) (exp 𝕂 𝕂 x) x :=
  (has_strict_deriv_at_exp_of_mem_ball hx).HasDerivAt

/--  The exponential map in a complete normed field `𝕂` of characteristic zero has strict derivative
`1` at zero, as long as it converges on a neighborhood of zero. -/
theorem has_strict_deriv_at_exp_zero_of_radius_pos (h : 0 < (expSeries 𝕂 𝕂).radius) : HasStrictDerivAt (exp 𝕂 𝕂) 1 0 :=
  (has_strict_fderiv_at_exp_zero_of_radius_pos h).HasStrictDerivAt

/--  The exponential map in a complete normed field `𝕂` of characteristic zero has derivative
`1` at zero, as long as it converges on a neighborhood of zero. -/
theorem has_deriv_at_exp_zero_of_radius_pos (h : 0 < (expSeries 𝕂 𝕂).radius) : HasDerivAt (exp 𝕂 𝕂) 1 0 :=
  (has_strict_deriv_at_exp_zero_of_radius_pos h).HasDerivAt

end deriv

section IsROrCAnyAlgebra

variable {𝕂 𝔸 : Type _} [IsROrC 𝕂] [NormedRing 𝔸] [NormedAlgebra 𝕂 𝔸] [CompleteSpace 𝔸]

/--  The exponential in a Banach-algebra `𝔸` over `𝕂 = ℝ` or `𝕂 = ℂ` has strict Fréchet-derivative
`1 : 𝔸 →L[𝕂] 𝔸` at zero. -/
theorem has_strict_fderiv_at_exp_zero : HasStrictFderivAt (exp 𝕂 𝔸) (1 : 𝔸 →L[𝕂] 𝔸) 0 :=
  has_strict_fderiv_at_exp_zero_of_radius_pos (exp_series_radius_pos 𝕂 𝔸)

/--  The exponential in a Banach-algebra `𝔸` over `𝕂 = ℝ` or `𝕂 = ℂ` has Fréchet-derivative
`1 : 𝔸 →L[𝕂] 𝔸` at zero. -/
theorem has_fderiv_at_exp_zero : HasFderivAt (exp 𝕂 𝔸) (1 : 𝔸 →L[𝕂] 𝔸) 0 :=
  has_strict_fderiv_at_exp_zero.HasFderivAt

end IsROrCAnyAlgebra

section IsROrCCommAlgebra

variable {𝕂 𝔸 : Type _} [IsROrC 𝕂] [NormedCommRing 𝔸] [NormedAlgebra 𝕂 𝔸] [CompleteSpace 𝔸]

attribute [local instance] char_zero_R_or_C

/--  The exponential map in a commutative Banach-algebra `𝔸` over `𝕂 = ℝ` or `𝕂 = ℂ` has strict
Fréchet-derivative `exp 𝕂 𝔸 x • 1 : 𝔸 →L[𝕂] 𝔸` at any point `x`. -/
theorem has_strict_fderiv_at_exp {x : 𝔸} : HasStrictFderivAt (exp 𝕂 𝔸) (exp 𝕂 𝔸 x • 1 : 𝔸 →L[𝕂] 𝔸) x :=
  has_strict_fderiv_at_exp_of_mem_ball ((exp_series_radius_eq_top 𝕂 𝔸).symm ▸ edist_lt_top _ _)

/--  The exponential map in a commutative Banach-algebra `𝔸` over `𝕂 = ℝ` or `𝕂 = ℂ` has
Fréchet-derivative `exp 𝕂 𝔸 x • 1 : 𝔸 →L[𝕂] 𝔸` at any point `x`. -/
theorem has_fderiv_at_exp {x : 𝔸} : HasFderivAt (exp 𝕂 𝔸) (exp 𝕂 𝔸 x • 1 : 𝔸 →L[𝕂] 𝔸) x :=
  has_strict_fderiv_at_exp.HasFderivAt

end IsROrCCommAlgebra

section DerivROrC

variable {𝕂 : Type _} [IsROrC 𝕂]

attribute [local instance] char_zero_R_or_C

/--  The exponential map in `𝕂 = ℝ` or `𝕂 = ℂ` has strict derivative `exp 𝕂 𝕂 x` at any point
`x`. -/
theorem has_strict_deriv_at_exp {x : 𝕂} : HasStrictDerivAt (exp 𝕂 𝕂) (exp 𝕂 𝕂 x) x :=
  has_strict_deriv_at_exp_of_mem_ball ((exp_series_radius_eq_top 𝕂 𝕂).symm ▸ edist_lt_top _ _)

/--  The exponential map in `𝕂 = ℝ` or `𝕂 = ℂ` has derivative `exp 𝕂 𝕂 x` at any point `x`. -/
theorem has_deriv_at_exp {x : 𝕂} : HasDerivAt (exp 𝕂 𝕂) (exp 𝕂 𝕂 x) x :=
  has_strict_deriv_at_exp.HasDerivAt

/--  The exponential map in `𝕂 = ℝ` or `𝕂 = ℂ` has strict derivative `1` at zero. -/
theorem has_strict_deriv_at_exp_zero : HasStrictDerivAt (exp 𝕂 𝕂) 1 0 :=
  has_strict_deriv_at_exp_zero_of_radius_pos (exp_series_radius_pos 𝕂 𝕂)

/--  The exponential map in `𝕂 = ℝ` or `𝕂 = ℂ` has derivative `1` at zero. -/
theorem has_deriv_at_exp_zero : HasDerivAt (exp 𝕂 𝕂) 1 0 :=
  has_strict_deriv_at_exp_zero.HasDerivAt

end DerivROrC

section Complex

theorem Complex.exp_eq_exp_ℂ_ℂ : Complex.exp = exp ℂ ℂ := by
  refine' funext fun x => _
  rw [Complex.exp, exp_eq_tsum_field]
  exact tendsto_nhds_unique x.exp'.tendsto_limit (exp_series_field_summable x).HasSum.tendsto_sum_nat

end Complex

section Real

theorem Real.exp_eq_exp_ℝ_ℝ : Real.exp = exp ℝ ℝ := by
  refine' funext fun x => _
  rw [Real.exp, Complex.exp_eq_exp_ℂ_ℂ, ← exp_ℝ_ℂ_eq_exp_ℂ_ℂ, exp_eq_tsum, exp_eq_tsum_field, ← re_to_complex, ←
    re_clm_apply, re_clm.map_tsum (exp_series_summable' (x : ℂ))]
  refine' tsum_congr fun n => _
  rw [re_clm.map_smul, ← Complex.of_real_pow, re_clm_apply, re_to_complex, Complex.of_real_re, smul_eq_mul, one_div,
    mul_commₓ, div_eq_mul_inv]

end Real

