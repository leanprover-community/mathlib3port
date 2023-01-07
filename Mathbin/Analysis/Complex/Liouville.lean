/-
Copyright (c) 2022 Yury G. Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury G. Kudryashov

! This file was ported from Lean 3 source module analysis.complex.liouville
! leanprover-community/mathlib commit 6afc9b06856ad973f6a2619e3e8a0a8d537a58f2
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Analysis.Complex.CauchyIntegral
import Mathbin.Analysis.Calculus.FderivAnalytic
import Mathbin.Analysis.NormedSpace.Completion

/-!
# Liouville's theorem

In this file we prove Liouville's theorem: if `f : E → F` is complex differentiable on the whole
space and its range is bounded, then the function is a constant. Various versions of this theorem
are formalized in `differentiable.apply_eq_apply_of_bounded`,
`differentiable.exists_const_forall_eq_of_bounded`, and
`differentiable.exists_eq_const_of_bounded`.

The proof is based on the Cauchy integral formula for the derivative of an analytic function, see
`complex.deriv_eq_smul_circle_integral`.
-/


open TopologicalSpace Metric Set Filter Asymptotics Function MeasureTheory

open TopologicalSpace Filter Nnreal Real

universe u v

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℂ E] {F : Type v} [NormedAddCommGroup F]
  [NormedSpace ℂ F]

-- mathport name: «expr ̂»
local postfix:100 "̂" => UniformSpace.Completion

namespace Complex

/-- If `f` is complex differentiable on an open disc with center `c` and radius `R > 0` and is
continuous on its closure, then `f' c` can be represented as an integral over the corresponding
circle.

TODO: add a version for `w ∈ metric.ball c R`.

TODO: add a version for higher derivatives. -/
theorem deriv_eq_smul_circle_integral [CompleteSpace F] {R : ℝ} {c : ℂ} {f : ℂ → F} (hR : 0 < R)
    (hf : DiffContOnCl ℂ f (ball c R)) :
    deriv f c = (2 * π * I : ℂ)⁻¹ • ∮ z in C(c, R), (z - c) ^ (-2 : ℤ) • f z :=
  by
  lift R to ℝ≥0 using hR.le
  refine' (hf.has_fpower_series_on_ball hR).HasFpowerSeriesAt.deriv.trans _
  simp only [cauchy_power_series_apply, one_div, zpow_neg, pow_one, smul_smul, zpow_two, mul_inv]
#align complex.deriv_eq_smul_circle_integral Complex.deriv_eq_smul_circle_integral

theorem norm_deriv_le_aux [CompleteSpace F] {c : ℂ} {R C : ℝ} {f : ℂ → F} (hR : 0 < R)
    (hf : DiffContOnCl ℂ f (ball c R)) (hC : ∀ z ∈ sphere c R, ‖f z‖ ≤ C) : ‖deriv f c‖ ≤ C / R :=
  by
  have : ∀ z ∈ sphere c R, ‖(z - c) ^ (-2 : ℤ) • f z‖ ≤ C / (R * R) :=
    fun z (hz : abs (z - c) = R) => by
    simpa [-mul_inv_rev, norm_smul, hz, zpow_two, ← div_eq_inv_mul] using
      (div_le_div_right (mul_pos hR hR)).2 (hC z hz)
  calc
    ‖deriv f c‖ = ‖(2 * π * I : ℂ)⁻¹ • ∮ z in C(c, R), (z - c) ^ (-2 : ℤ) • f z‖ :=
      congr_arg norm (deriv_eq_smul_circle_integral hR hf)
    _ ≤ R * (C / (R * R)) :=
      circleIntegral.norm_two_pi_I_inv_smul_integral_le_of_norm_le_const hR.le this
    _ = C / R := by rw [mul_div_left_comm, div_self_mul_self', div_eq_mul_inv]
    
#align complex.norm_deriv_le_aux Complex.norm_deriv_le_aux

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers
      [(Command.docComment
        "/--"
        "If `f` is complex differentiable on an open disc of radius `R > 0`, is continuous on its\nclosure, and its values on the boundary circle of this disc are bounded from above by `C`, then the\nnorm of its derivative at the center is at most `C / R`. -/")]
      []
      []
      []
      []
      [])
     (Command.theorem
      "theorem"
      (Command.declId `norm_deriv_le_of_forall_mem_sphere_norm_le [])
      (Command.declSig
       [(Term.implicitBinder "{" [`c] [":" (Data.Complex.Basic.termℂ "ℂ")] "}")
        (Term.implicitBinder "{" [`R `C] [":" (Data.Real.Basic.termℝ "ℝ")] "}")
        (Term.implicitBinder "{" [`f] [":" (Term.arrow (Data.Complex.Basic.termℂ "ℂ") "→" `F)] "}")
        (Term.explicitBinder "(" [`hR] [":" («term_<_» (num "0") "<" `R)] [] ")")
        (Term.explicitBinder
         "("
         [`hd]
         [":" (Term.app `DiffContOnCl [(Data.Complex.Basic.termℂ "ℂ") `f (Term.app `ball [`c `R])])]
         []
         ")")
        (Term.explicitBinder
         "("
         [`hC]
         [":"
          (Std.ExtendedBinder.«term∀__,_»
           "∀"
           (Lean.binderIdent `z)
           («binderTerm∈_» "∈" (Term.app `sphere [`c `R]))
           ","
           («term_≤_» (Analysis.Normed.Group.Basic.«term‖_‖» "‖" (Term.app `f [`z]) "‖") "≤" `C))]
         []
         ")")]
       (Term.typeSpec
        ":"
        («term_≤_»
         (Analysis.Normed.Group.Basic.«term‖_‖» "‖" (Term.app `deriv [`f `c]) "‖")
         "≤"
         («term_/_» `C "/" `R))))
      (Command.declValSimple
       ":="
       (Term.byTactic
        "by"
        (Tactic.tacticSeq
         (Tactic.tacticSeq1Indented
          [(Mathlib.Tactic.set
            "set"
            []
            (Mathlib.Tactic.setArgsRest
             `e
             [":"
              (Topology.Algebra.Module.Basic.«term_→L[_]_»
               `F
               " →L["
               (Data.Complex.Basic.termℂ "ℂ")
               "] "
               (Analysis.Complex.Liouville.«term_̂» `F "̂"))]
             ":="
             `UniformSpace.Completion.toComplL
             []))
           []
           (Tactic.tacticHave_
            "have"
            (Term.haveDecl
             (Term.haveIdDecl
              []
              [(Term.typeSpec
                ":"
                (Term.app
                 `HasDerivAt
                 [(«term_∘_» `e "∘" `f) (Term.app `e [(Term.app `deriv [`f `c])]) `c]))]
              ":="
              (Term.app
               `e.has_fderiv_at.comp_has_deriv_at
               [`c
                (Term.proj
                 («term_<|_»
                  (Term.app `hd.differentiable_at [`is_open_ball])
                  "<|"
                  (Term.app `mem_ball_self [`hR]))
                 "."
                 `HasDerivAt)]))))
           []
           (calcTactic
            "calc"
            (calcStep
             («term_=_»
              (Analysis.Normed.Group.Basic.«term‖_‖» "‖" (Term.app `deriv [`f `c]) "‖")
              "="
              (Analysis.Normed.Group.Basic.«term‖_‖»
               "‖"
               (Term.app `deriv [(«term_∘_» `e "∘" `f) `c])
               "‖"))
             ":="
             (Term.byTactic
              "by"
              (Tactic.tacticSeq
               (Tactic.tacticSeq1Indented
                [(Tactic.rwSeq
                  "rw"
                  []
                  (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `this.deriv)] "]")
                  [])
                 []
                 (Tactic.exact
                  "exact"
                  (Term.proj
                   (Term.app `UniformSpace.Completion.norm_coe [(Term.hole "_")])
                   "."
                   `symm))]))))
            [(calcStep
              («term_≤_» (Term.hole "_") "≤" («term_/_» `C "/" `R))
              ":="
              (Term.app
               `norm_deriv_le_aux
               [`hR
                (Term.app `e.differentiable.comp_diff_cont_on_cl [`hd])
                (Term.fun
                 "fun"
                 (Term.basicFun
                  [`z `hz]
                  []
                  "=>"
                  (Term.app
                   (Term.proj
                    (Term.app `UniformSpace.Completion.norm_coe [(Term.hole "_")])
                    "."
                    `trans_le)
                   [(Term.app `hC [`z `hz])])))]))])])))
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
         [(Mathlib.Tactic.set
           "set"
           []
           (Mathlib.Tactic.setArgsRest
            `e
            [":"
             (Topology.Algebra.Module.Basic.«term_→L[_]_»
              `F
              " →L["
              (Data.Complex.Basic.termℂ "ℂ")
              "] "
              (Analysis.Complex.Liouville.«term_̂» `F "̂"))]
            ":="
            `UniformSpace.Completion.toComplL
            []))
          []
          (Tactic.tacticHave_
           "have"
           (Term.haveDecl
            (Term.haveIdDecl
             []
             [(Term.typeSpec
               ":"
               (Term.app
                `HasDerivAt
                [(«term_∘_» `e "∘" `f) (Term.app `e [(Term.app `deriv [`f `c])]) `c]))]
             ":="
             (Term.app
              `e.has_fderiv_at.comp_has_deriv_at
              [`c
               (Term.proj
                («term_<|_»
                 (Term.app `hd.differentiable_at [`is_open_ball])
                 "<|"
                 (Term.app `mem_ball_self [`hR]))
                "."
                `HasDerivAt)]))))
          []
          (calcTactic
           "calc"
           (calcStep
            («term_=_»
             (Analysis.Normed.Group.Basic.«term‖_‖» "‖" (Term.app `deriv [`f `c]) "‖")
             "="
             (Analysis.Normed.Group.Basic.«term‖_‖»
              "‖"
              (Term.app `deriv [(«term_∘_» `e "∘" `f) `c])
              "‖"))
            ":="
            (Term.byTactic
             "by"
             (Tactic.tacticSeq
              (Tactic.tacticSeq1Indented
               [(Tactic.rwSeq
                 "rw"
                 []
                 (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `this.deriv)] "]")
                 [])
                []
                (Tactic.exact
                 "exact"
                 (Term.proj
                  (Term.app `UniformSpace.Completion.norm_coe [(Term.hole "_")])
                  "."
                  `symm))]))))
           [(calcStep
             («term_≤_» (Term.hole "_") "≤" («term_/_» `C "/" `R))
             ":="
             (Term.app
              `norm_deriv_le_aux
              [`hR
               (Term.app `e.differentiable.comp_diff_cont_on_cl [`hd])
               (Term.fun
                "fun"
                (Term.basicFun
                 [`z `hz]
                 []
                 "=>"
                 (Term.app
                  (Term.proj
                   (Term.app `UniformSpace.Completion.norm_coe [(Term.hole "_")])
                   "."
                   `trans_le)
                  [(Term.app `hC [`z `hz])])))]))])])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (calcTactic
       "calc"
       (calcStep
        («term_=_»
         (Analysis.Normed.Group.Basic.«term‖_‖» "‖" (Term.app `deriv [`f `c]) "‖")
         "="
         (Analysis.Normed.Group.Basic.«term‖_‖»
          "‖"
          (Term.app `deriv [(«term_∘_» `e "∘" `f) `c])
          "‖"))
        ":="
        (Term.byTactic
         "by"
         (Tactic.tacticSeq
          (Tactic.tacticSeq1Indented
           [(Tactic.rwSeq "rw" [] (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `this.deriv)] "]") [])
            []
            (Tactic.exact
             "exact"
             (Term.proj
              (Term.app `UniformSpace.Completion.norm_coe [(Term.hole "_")])
              "."
              `symm))]))))
       [(calcStep
         («term_≤_» (Term.hole "_") "≤" («term_/_» `C "/" `R))
         ":="
         (Term.app
          `norm_deriv_le_aux
          [`hR
           (Term.app `e.differentiable.comp_diff_cont_on_cl [`hd])
           (Term.fun
            "fun"
            (Term.basicFun
             [`z `hz]
             []
             "=>"
             (Term.app
              (Term.proj
               (Term.app `UniformSpace.Completion.norm_coe [(Term.hole "_")])
               "."
               `trans_le)
              [(Term.app `hC [`z `hz])])))]))])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       `norm_deriv_le_aux
       [`hR
        (Term.app `e.differentiable.comp_diff_cont_on_cl [`hd])
        (Term.fun
         "fun"
         (Term.basicFun
          [`z `hz]
          []
          "=>"
          (Term.app
           (Term.proj (Term.app `UniformSpace.Completion.norm_coe [(Term.hole "_")]) "." `trans_le)
           [(Term.app `hC [`z `hz])])))])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.fun
       "fun"
       (Term.basicFun
        [`z `hz]
        []
        "=>"
        (Term.app
         (Term.proj (Term.app `UniformSpace.Completion.norm_coe [(Term.hole "_")]) "." `trans_le)
         [(Term.app `hC [`z `hz])])))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       (Term.proj (Term.app `UniformSpace.Completion.norm_coe [(Term.hole "_")]) "." `trans_le)
       [(Term.app `hC [`z `hz])])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `hC [`z `hz])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `hz
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `z
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `hC
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren "(" (Term.app `hC [`z `hz]) ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (Term.proj (Term.app `UniformSpace.Completion.norm_coe [(Term.hole "_")]) "." `trans_le)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.app `UniformSpace.Completion.norm_coe [(Term.hole "_")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `UniformSpace.Completion.norm_coe
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.app `UniformSpace.Completion.norm_coe [(Term.hole "_")])
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
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, term))
      (Term.app `e.differentiable.comp_diff_cont_on_cl [`hd])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `hd
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `e.differentiable.comp_diff_cont_on_cl
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023,
     term) <=? (some 1023, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.app `e.differentiable.comp_diff_cont_on_cl [`hd])
     ")")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `hR
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `norm_deriv_le_aux
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_≤_» (Term.hole "_") "≤" («term_/_» `C "/" `R))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_/_» `C "/" `R)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `R
[PrettyPrinter.parenthesize] ...precedences are 71 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 70, term))
      `C
[PrettyPrinter.parenthesize] ...precedences are 70 >? 1024, (none, [anonymous]) <=? (some 70, term)
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
         [(Tactic.rwSeq "rw" [] (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `this.deriv)] "]") [])
          []
          (Tactic.exact
           "exact"
           (Term.proj (Term.app `UniformSpace.Completion.norm_coe [(Term.hole "_")]) "." `symm))])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.exact
       "exact"
       (Term.proj (Term.app `UniformSpace.Completion.norm_coe [(Term.hole "_")]) "." `symm))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.proj (Term.app `UniformSpace.Completion.norm_coe [(Term.hole "_")]) "." `symm)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.app `UniformSpace.Completion.norm_coe [(Term.hole "_")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `UniformSpace.Completion.norm_coe
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.app `UniformSpace.Completion.norm_coe [(Term.hole "_")])
     ")")
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.rwSeq "rw" [] (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `this.deriv)] "]") [])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `this.deriv
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, tactic) <=? (none, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_=_»
       (Analysis.Normed.Group.Basic.«term‖_‖» "‖" (Term.app `deriv [`f `c]) "‖")
       "="
       (Analysis.Normed.Group.Basic.«term‖_‖» "‖" (Term.app `deriv [(«term_∘_» `e "∘" `f) `c]) "‖"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Analysis.Normed.Group.Basic.«term‖_‖» "‖" (Term.app `deriv [(«term_∘_» `e "∘" `f) `c]) "‖")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `deriv [(«term_∘_» `e "∘" `f) `c])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `c
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_∘_»', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_∘_»', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      («term_∘_» `e "∘" `f)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `f
[PrettyPrinter.parenthesize] ...precedences are 90 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 90, term))
      `e
[PrettyPrinter.parenthesize] ...precedences are 91 >? 1024, (none, [anonymous]) <=? (some 90, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 90, (some 90, term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren "(" («term_∘_» `e "∘" `f) ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `deriv
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 50, term))
      (Analysis.Normed.Group.Basic.«term‖_‖» "‖" (Term.app `deriv [`f `c]) "‖")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `deriv [`f `c])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `c
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `f
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `deriv
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
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
            `HasDerivAt
            [(«term_∘_» `e "∘" `f) (Term.app `e [(Term.app `deriv [`f `c])]) `c]))]
         ":="
         (Term.app
          `e.has_fderiv_at.comp_has_deriv_at
          [`c
           (Term.proj
            («term_<|_»
             (Term.app `hd.differentiable_at [`is_open_ball])
             "<|"
             (Term.app `mem_ball_self [`hR]))
            "."
            `HasDerivAt)]))))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       `e.has_fderiv_at.comp_has_deriv_at
       [`c
        (Term.proj
         («term_<|_»
          (Term.app `hd.differentiable_at [`is_open_ball])
          "<|"
          (Term.app `mem_ball_self [`hR]))
         "."
         `HasDerivAt)])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.proj', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.proj', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.proj
       («term_<|_»
        (Term.app `hd.differentiable_at [`is_open_ball])
        "<|"
        (Term.app `mem_ball_self [`hR]))
       "."
       `HasDerivAt)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      («term_<|_»
       (Term.app `hd.differentiable_at [`is_open_ball])
       "<|"
       (Term.app `mem_ball_self [`hR]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `mem_ball_self [`hR])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `hR
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `mem_ball_self
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 10 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 10, term))
      (Term.app `hd.differentiable_at [`is_open_ball])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `is_open_ball
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `hd.differentiable_at
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (some 10, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 10, (some 10, term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     («term_<|_»
      (Term.app `hd.differentiable_at [`is_open_ball])
      "<|"
      (Term.app `mem_ball_self [`hR]))
     ")")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `c
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `e.has_fderiv_at.comp_has_deriv_at
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `HasDerivAt [(«term_∘_» `e "∘" `f) (Term.app `e [(Term.app `deriv [`f `c])]) `c])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `c
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.app `e [(Term.app `deriv [`f `c])])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `deriv [`f `c])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `c
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `f
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `deriv
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren "(" (Term.app `deriv [`f `c]) ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `e
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023,
     term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.app `e [(Term.paren "(" (Term.app `deriv [`f `c]) ")")])
     ")")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_∘_»', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_∘_»', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      («term_∘_» `e "∘" `f)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `f
[PrettyPrinter.parenthesize] ...precedences are 90 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 90, term))
      `e
[PrettyPrinter.parenthesize] ...precedences are 91 >? 1024, (none, [anonymous]) <=? (some 90, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 90, (some 90, term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren "(" («term_∘_» `e "∘" `f) ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `HasDerivAt
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Mathlib.Tactic.set
       "set"
       []
       (Mathlib.Tactic.setArgsRest
        `e
        [":"
         (Topology.Algebra.Module.Basic.«term_→L[_]_»
          `F
          " →L["
          (Data.Complex.Basic.termℂ "ℂ")
          "] "
          (Analysis.Complex.Liouville.«term_̂» `F "̂"))]
        ":="
        `UniformSpace.Completion.toComplL
        []))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `UniformSpace.Completion.toComplL
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Topology.Algebra.Module.Basic.«term_→L[_]_»
       `F
       " →L["
       (Data.Complex.Basic.termℂ "ℂ")
       "] "
       (Analysis.Complex.Liouville.«term_̂» `F "̂"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Analysis.Complex.Liouville.«term_̂» `F "̂")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Analysis.Complex.Liouville.«term_̂»', expected 'Analysis.Complex.Liouville.term_̂._@.Analysis.Complex.Liouville._hyg.8'
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
    If `f` is complex differentiable on an open disc of radius `R > 0`, is continuous on its
    closure, and its values on the boundary circle of this disc are bounded from above by `C`, then the
    norm of its derivative at the center is at most `C / R`. -/
  theorem
    norm_deriv_le_of_forall_mem_sphere_norm_le
    { c : ℂ }
        { R C : ℝ }
        { f : ℂ → F }
        ( hR : 0 < R )
        ( hd : DiffContOnCl ℂ f ball c R )
        ( hC : ∀ z ∈ sphere c R , ‖ f z ‖ ≤ C )
      : ‖ deriv f c ‖ ≤ C / R
    :=
      by
        set e : F →L[ ℂ ] F ̂ := UniformSpace.Completion.toComplL
          have
            : HasDerivAt e ∘ f e deriv f c c
              :=
              e.has_fderiv_at.comp_has_deriv_at
                c hd.differentiable_at is_open_ball <| mem_ball_self hR . HasDerivAt
          calc
            ‖ deriv f c ‖ = ‖ deriv e ∘ f c ‖
              :=
              by rw [ this.deriv ] exact UniformSpace.Completion.norm_coe _ . symm
            _ ≤ C / R
              :=
              norm_deriv_le_aux
                hR
                  e.differentiable.comp_diff_cont_on_cl hd
                  fun z hz => UniformSpace.Completion.norm_coe _ . trans_le hC z hz
#align
  complex.norm_deriv_le_of_forall_mem_sphere_norm_le Complex.norm_deriv_le_of_forall_mem_sphere_norm_le

/-- An auxiliary lemma for Liouville's theorem `differentiable.apply_eq_apply_of_bounded`. -/
theorem liouville_theorem_aux {f : ℂ → F} (hf : Differentiable ℂ f) (hb : Bounded (range f))
    (z w : ℂ) : f z = f w := by
  suffices : ∀ c, deriv f c = 0
  exact is_const_of_deriv_eq_zero hf this z w
  clear z w
  intro c
  obtain ⟨C, C₀, hC⟩ : ∃ C > (0 : ℝ), ∀ z, ‖f z‖ ≤ C :=
    by
    rcases bounded_iff_forall_norm_le.1 hb with ⟨C, hC⟩
    exact
      ⟨max C 1, lt_max_iff.2 (Or.inr zero_lt_one), fun z =>
        (hC (f z) (mem_range_self _)).trans (le_max_left _ _)⟩
  refine' norm_le_zero_iff.1 (le_of_forall_le_of_dense fun ε ε₀ => _)
  calc
    ‖deriv f c‖ ≤ C / (C / ε) :=
      norm_deriv_le_of_forall_mem_sphere_norm_le (div_pos C₀ ε₀) hf.diff_cont_on_cl fun z _ => hC z
    _ = ε := div_div_cancel' C₀.lt.ne'
    
#align complex.liouville_theorem_aux Complex.liouville_theorem_aux

end Complex

namespace Differentiable

open Complex

/-- **Liouville's theorem**: a complex differentiable bounded function `f : E → F` is a constant. -/
theorem apply_eq_apply_of_bounded {f : E → F} (hf : Differentiable ℂ f) (hb : Bounded (range f))
    (z w : E) : f z = f w :=
  by
  set g : ℂ → F := f ∘ fun t : ℂ => t • (w - z) + z
  suffices g 0 = g 1 by simpa [g]
  apply liouville_theorem_aux
  exacts[hf.comp ((differentiable_id.smul_const (w - z)).AddConst z),
    hb.mono (range_comp_subset_range _ _)]
#align differentiable.apply_eq_apply_of_bounded Differentiable.apply_eq_apply_of_bounded

/-- **Liouville's theorem**: a complex differentiable bounded function is a constant. -/
theorem exists_const_forall_eq_of_bounded {f : E → F} (hf : Differentiable ℂ f)
    (hb : Bounded (range f)) : ∃ c, ∀ z, f z = c :=
  ⟨f 0, fun z => hf.apply_eq_apply_of_bounded hb _ _⟩
#align
  differentiable.exists_const_forall_eq_of_bounded Differentiable.exists_const_forall_eq_of_bounded

/-- **Liouville's theorem**: a complex differentiable bounded function is a constant. -/
theorem exists_eq_const_of_bounded {f : E → F} (hf : Differentiable ℂ f) (hb : Bounded (range f)) :
    ∃ c, f = const E c :=
  (hf.exists_const_forall_eq_of_bounded hb).imp fun c => funext
#align differentiable.exists_eq_const_of_bounded Differentiable.exists_eq_const_of_bounded

end Differentiable

