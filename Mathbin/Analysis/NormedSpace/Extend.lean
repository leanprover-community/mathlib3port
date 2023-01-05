/-
Copyright (c) 2020 Ruben Van de Velde. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ruben Van de Velde

! This file was ported from Lean 3 source module analysis.normed_space.extend
! leanprover-community/mathlib commit 6d0adfa76594f304b4650d098273d4366edeb61b
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Algebra.Algebra.RestrictScalars
import Mathbin.Data.Complex.IsROrC

/-!
# Extending a continuous `ℝ`-linear map to a continuous `𝕜`-linear map

In this file we provide a way to extend a continuous `ℝ`-linear map to a continuous `𝕜`-linear map
in a way that bounds the norm by the norm of the original map, when `𝕜` is either `ℝ` (the
extension is trivial) or `ℂ`. We formulate the extension uniformly, by assuming `is_R_or_C 𝕜`.

We motivate the form of the extension as follows. Note that `fc : F →ₗ[𝕜] 𝕜` is determined fully by
`Re fc`: for all `x : F`, `fc (I • x) = I * fc x`, so `Im (fc x) = -Re (fc (I • x))`. Therefore,
given an `fr : F →ₗ[ℝ] ℝ`, we define `fc x = fr x - fr (I • x) * I`.

## Main definitions

* `linear_map.extend_to_𝕜`
* `continuous_linear_map.extend_to_𝕜`

## Implementation details

For convenience, the main definitions above operate in terms of `restrict_scalars ℝ 𝕜 F`.
Alternate forms which operate on `[is_scalar_tower ℝ 𝕜 F]` instead are provided with a primed name.

-/


open IsROrC

variable {𝕜 : Type _} [IsROrC 𝕜] {F : Type _} [SeminormedAddCommGroup F] [NormedSpace 𝕜 F]

-- mathport name: exprabs𝕜
local notation "abs𝕜" => @IsROrC.abs 𝕜 _

/-- Extend `fr : F →ₗ[ℝ] ℝ` to `F →ₗ[𝕜] 𝕜` in a way that will also be continuous and have its norm
bounded by `‖fr‖` if `fr` is continuous. -/
noncomputable def LinearMap.extendTo𝕜' [Module ℝ F] [IsScalarTower ℝ 𝕜 F] (fr : F →ₗ[ℝ] ℝ) :
    F →ₗ[𝕜] 𝕜 :=
  by
  let fc : F → 𝕜 := fun x => (fr x : 𝕜) - (I : 𝕜) * fr ((I : 𝕜) • x)
  have add : ∀ x y : F, fc (x + y) = fc x + fc y :=
    by
    intro x y
    simp only [fc]
    simp only [smul_add, LinearMap.map_add, of_real_add]
    rw [mul_add]
    abel
  have A : ∀ (c : ℝ) (x : F), (fr ((c : 𝕜) • x) : 𝕜) = (c : 𝕜) * (fr x : 𝕜) :=
    by
    intro c x
    rw [← of_real_mul]
    congr 1
    rw [IsROrC.of_real_alg, smul_assoc, fr.map_smul, Algebra.id.smul_eq_mul, one_smul]
  have smul_ℝ : ∀ (c : ℝ) (x : F), fc ((c : 𝕜) • x) = (c : 𝕜) * fc x :=
    by
    intro c x
    simp only [fc, A]
    rw [A c x]
    rw [smul_smul, mul_comm I (c : 𝕜), ← smul_smul, A, mul_sub]
    ring
  have smul_I : ∀ x : F, fc ((I : 𝕜) • x) = (I : 𝕜) * fc x :=
    by
    intro x
    simp only [fc]
    cases' @I_mul_I_ax 𝕜 _ with h h
    · simp [h]
    rw [mul_sub, ← mul_assoc, smul_smul, h]
    simp only [neg_mul, LinearMap.map_neg, one_mul, one_smul, mul_neg, of_real_neg, neg_smul,
      sub_neg_eq_add, add_comm]
  have smul_𝕜 : ∀ (c : 𝕜) (x : F), fc (c • x) = c • fc x :=
    by
    intro c x
    rw [← re_add_im c, add_smul, add_smul, add, smul_ℝ, ← smul_smul, smul_ℝ, smul_I, ← mul_assoc]
    rfl
  exact
    { toFun := fc
      map_add' := add
      map_smul' := smul_𝕜 }
#align linear_map.extend_to_𝕜' LinearMap.extendTo𝕜'

theorem LinearMap.extend_to_𝕜'_apply [Module ℝ F] [IsScalarTower ℝ 𝕜 F] (fr : F →ₗ[ℝ] ℝ) (x : F) :
    fr.extendTo𝕜' x = (fr x : 𝕜) - (i : 𝕜) * fr ((i : 𝕜) • x) :=
  rfl
#align linear_map.extend_to_𝕜'_apply LinearMap.extend_to_𝕜'_apply

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers
      [(Command.docComment "/--" "The norm of the extension is bounded by `‖fr‖`. -/")]
      []
      []
      []
      []
      [])
     (Command.theorem
      "theorem"
      (Command.declId `norm_bound [])
      (Command.declSig
       [(Term.instBinder "[" [] (Term.app `NormedSpace [(Data.Real.Basic.termℝ "ℝ") `F]) "]")
        (Term.instBinder "[" [] (Term.app `IsScalarTower [(Data.Real.Basic.termℝ "ℝ") `𝕜 `F]) "]")
        (Term.explicitBinder
         "("
         [`fr]
         [":"
          (Topology.Algebra.Module.Basic.«term_→L[_]_»
           `F
           " →L["
           (Data.Real.Basic.termℝ "ℝ")
           "] "
           (Data.Real.Basic.termℝ "ℝ"))]
         []
         ")")
        (Term.explicitBinder "(" [`x] [":" `F] [] ")")]
       (Term.typeSpec
        ":"
        («term_≤_»
         (Analysis.Normed.Group.Basic.«term‖_‖»
          "‖"
          (Term.typeAscription
           "("
           (Term.app (Term.proj (Term.proj `fr "." `toLinearMap) "." `extendTo𝕜') [`x])
           ":"
           [`𝕜]
           ")")
          "‖")
         "≤"
         («term_*_»
          (Analysis.Normed.Group.Basic.«term‖_‖» "‖" `fr "‖")
          "*"
          (Analysis.Normed.Group.Basic.«term‖_‖» "‖" `x "‖")))))
      (Command.declValSimple
       ":="
       (Term.byTactic
        "by"
        (Tactic.tacticSeq
         (Tactic.tacticSeq1Indented
          [(Tactic.tacticLet_
            "let"
            (Term.letDecl
             (Term.letIdDecl
              `lm
              []
              [(Term.typeSpec ":" (Algebra.Module.LinearMap.«term_→ₗ[_]_» `F " →ₗ[" `𝕜 "] " `𝕜))]
              ":="
              `fr.to_linear_map.extend_to_𝕜')))
           []
           (Mathlib.Tactic.tacticClassical_
            "classical"
            (Tactic.tacticSeq
             (Tactic.tacticSeq1Indented
              [(Classical.«tacticBy_cases_:_»
                "by_cases"
                [`h ":"]
                («term_=_» (Term.app `lm [`x]) "=" (num "0")))
               []
               (tactic__
                (cdotTk (patternIgnore (token.«· » "·")))
                [(Tactic.rwSeq
                  "rw"
                  []
                  (Tactic.rwRuleSeq
                   "["
                   [(Tactic.rwRule [] `h) "," (Tactic.rwRule [] `norm_zero)]
                   "]")
                  [])
                 []
                 (Tactic.«tactic_<;>_»
                  (Tactic.apply "apply" `mul_nonneg)
                  "<;>"
                  (Tactic.exact "exact" (Term.app `norm_nonneg [(Term.hole "_")])))])
               []
               (Tactic.tacticLet_
                "let"
                (Term.letDecl (Term.letIdDecl `fx [] [] ":=" («term_⁻¹» (Term.app `lm [`x]) "⁻¹"))))
               []
               (Tactic.tacticLet_
                "let"
                (Term.letDecl
                 (Term.letIdDecl
                  `t
                  []
                  []
                  ":="
                  («term_/_»
                   `fx
                   "/"
                   (Term.typeAscription
                    "("
                    (Term.app (Analysis.NormedSpace.Extend.termabs𝕜 "abs𝕜") [`fx])
                    ":"
                    [`𝕜]
                    ")")))))
               []
               (Tactic.tacticHave_
                "have"
                (Term.haveDecl
                 (Term.haveIdDecl
                  [`ht []]
                  [(Term.typeSpec
                    ":"
                    («term_=_»
                     (Term.app (Analysis.NormedSpace.Extend.termabs𝕜 "abs𝕜") [`t])
                     "="
                     (num "1")))]
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
                       [(Tactic.simpArgs
                         "["
                         [(Tactic.simpLemma [] [] `abs_of_real)
                          ","
                          (Tactic.simpLemma [] [] `of_real_inv)
                          ","
                          (Tactic.simpLemma [] [] `IsROrC.abs_inv)
                          ","
                          (Tactic.simpLemma [] [] `IsROrC.abs_div)
                          ","
                          (Tactic.simpLemma [] [] `IsROrC.abs_abs)
                          ","
                          (Tactic.simpLemma [] [] `h)]
                         "]")]
                       [])]))))))
               []
               (Tactic.tacticHave_
                "have"
                (Term.haveDecl
                 (Term.haveIdDecl
                  [`h1 []]
                  [(Term.typeSpec
                    ":"
                    («term_=_»
                     (Term.typeAscription
                      "("
                      (Term.app `fr [(Algebra.Group.Defs.«term_•_» `t " • " `x)])
                      ":"
                      [`𝕜]
                      ")")
                     "="
                     (Term.app `lm [(Algebra.Group.Defs.«term_•_» `t " • " `x)])))]
                  ":="
                  (Term.byTactic
                   "by"
                   (Tactic.tacticSeq
                    (Tactic.tacticSeq1Indented
                     [(Tactic.apply "apply" `ext)
                      []
                      (tactic__
                       (cdotTk (patternIgnore (token.«· » "·")))
                       [(Tactic.simp
                         "simp"
                         []
                         []
                         ["only"]
                         ["["
                          [(Tactic.simpLemma [] [] `lm)
                           ","
                           (Tactic.simpLemma [] [] `of_real_re)
                           ","
                           (Tactic.simpLemma [] [] `LinearMap.extend_to_𝕜'_apply)
                           ","
                           (Tactic.simpLemma [] [] `mul_re)
                           ","
                           (Tactic.simpLemma [] [] `I_re)
                           ","
                           (Tactic.simpLemma [] [] `of_real_im)
                           ","
                           (Tactic.simpLemma [] [] `zero_mul)
                           ","
                           (Tactic.simpLemma [] [] `AddMonoidHom.map_sub)
                           ","
                           (Tactic.simpLemma [] [] `sub_zero)
                           ","
                           (Tactic.simpLemma [] [] `mul_zero)]
                          "]"]
                         [])
                        []
                        (Tactic.tacticRfl "rfl")])
                      []
                      (tactic__
                       (cdotTk (patternIgnore (token.«· » "·")))
                       [(Mathlib.Tactic.tacticSymm_ "symm" [])
                        []
                        (calcTactic
                         "calc"
                         (calcStep
                          («term_=_»
                           (Term.app
                            `im
                            [(Term.app `lm [(Algebra.Group.Defs.«term_•_» `t " • " `x)])])
                           "="
                           (Term.app `im [(«term_*_» `t "*" (Term.app `lm [`x]))]))
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
                                [(Tactic.rwRule [] `lm.map_smul)
                                 ","
                                 (Tactic.rwRule [] `smul_eq_mul)]
                                "]")
                               [])]))))
                         [(calcStep
                           («term_=_»
                            (Term.hole "_")
                            "="
                            (Term.app
                             `im
                             [(«term_*_»
                               («term_/_»
                                («term_⁻¹» (Term.app `lm [`x]) "⁻¹")
                                "/"
                                (Term.app
                                 (Analysis.NormedSpace.Extend.termabs𝕜 "abs𝕜")
                                 [(«term_⁻¹» (Term.app `lm [`x]) "⁻¹")]))
                               "*"
                               (Term.app `lm [`x]))]))
                           ":="
                           `rfl)
                          (calcStep
                           («term_=_»
                            (Term.hole "_")
                            "="
                            (Term.app
                             `im
                             [(«term_/_»
                               (num "1")
                               "/"
                               (Term.typeAscription
                                "("
                                (Term.app
                                 (Analysis.NormedSpace.Extend.termabs𝕜 "abs𝕜")
                                 [(«term_⁻¹» (Term.app `lm [`x]) "⁻¹")])
                                ":"
                                [`𝕜]
                                ")"))]))
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
                                 [(Tactic.rwRule [] `div_mul_eq_mul_div)
                                  ","
                                  (Tactic.rwRule [] (Term.app `inv_mul_cancel [`h]))]
                                 "]")
                                [])]))))
                          (calcStep
                           («term_=_» (Term.hole "_") "=" (num "0"))
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
                                 [(Tactic.rwRule [(patternIgnore (token.«← » "←"))] `of_real_one)
                                  ","
                                  (Tactic.rwRule [(patternIgnore (token.«← » "←"))] `of_real_div)
                                  ","
                                  (Tactic.rwRule [] `of_real_im)]
                                 "]")
                                [])]))))
                          (calcStep
                           («term_=_»
                            (Term.hole "_")
                            "="
                            (Term.app
                             `im
                             [(Term.typeAscription
                               "("
                               (Term.app `fr [(Algebra.Group.Defs.«term_•_» `t " • " `x)])
                               ":"
                               [`𝕜]
                               ")")]))
                           ":="
                           (Term.byTactic
                            "by"
                            (Tactic.tacticSeq
                             (Tactic.tacticSeq1Indented
                              [(Tactic.rwSeq
                                "rw"
                                []
                                (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `of_real_im)] "]")
                                [])]))))])])]))))))
               []
               (calcTactic
                "calc"
                (calcStep
                 («term_=_»
                  (Analysis.Normed.Group.Basic.«term‖_‖» "‖" (Term.app `lm [`x]) "‖")
                  "="
                  («term_*_»
                   (Term.app (Analysis.NormedSpace.Extend.termabs𝕜 "abs𝕜") [`t])
                   "*"
                   (Analysis.Normed.Group.Basic.«term‖_‖» "‖" (Term.app `lm [`x]) "‖")))
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
                       [(Tactic.rwRule [] `ht) "," (Tactic.rwRule [] `one_mul)]
                       "]")
                      [])]))))
                [(calcStep
                  («term_=_»
                   (Term.hole "_")
                   "="
                   (Analysis.Normed.Group.Basic.«term‖_‖»
                    "‖"
                    («term_*_» `t "*" (Term.app `lm [`x]))
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
                        [(Tactic.rwRule [(patternIgnore (token.«← » "←"))] `norm_eq_abs)
                         ","
                         (Tactic.rwRule [] `norm_mul)]
                        "]")
                       [])]))))
                 (calcStep
                  («term_=_»
                   (Term.hole "_")
                   "="
                   (Analysis.Normed.Group.Basic.«term‖_‖»
                    "‖"
                    (Term.app `lm [(Algebra.Group.Defs.«term_•_» `t " • " `x)])
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
                        [(Tactic.rwRule [(patternIgnore (token.«← » "←"))] `smul_eq_mul)
                         ","
                         (Tactic.rwRule [] `lm.map_smul)]
                        "]")
                       [])]))))
                 (calcStep
                  («term_=_»
                   (Term.hole "_")
                   "="
                   (Analysis.Normed.Group.Basic.«term‖_‖»
                    "‖"
                    (Term.typeAscription
                     "("
                     (Term.app `fr [(Algebra.Group.Defs.«term_•_» `t " • " `x)])
                     ":"
                     [`𝕜]
                     ")")
                    "‖"))
                  ":="
                  (Term.byTactic
                   "by"
                   (Tactic.tacticSeq
                    (Tactic.tacticSeq1Indented
                     [(Tactic.rwSeq
                       "rw"
                       []
                       (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `h1)] "]")
                       [])]))))
                 (calcStep
                  («term_=_»
                   (Term.hole "_")
                   "="
                   (Analysis.Normed.Group.Basic.«term‖_‖»
                    "‖"
                    (Term.app `fr [(Algebra.Group.Defs.«term_•_» `t " • " `x)])
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
                        [(Tactic.rwRule [] `norm_eq_abs)
                         ","
                         (Tactic.rwRule [] `abs_of_real)
                         ","
                         (Tactic.rwRule [] `norm_eq_abs)
                         ","
                         (Tactic.rwRule [] `abs_to_real)]
                        "]")
                       [])]))))
                 (calcStep
                  («term_≤_»
                   (Term.hole "_")
                   "≤"
                   («term_*_»
                    (Analysis.Normed.Group.Basic.«term‖_‖» "‖" `fr "‖")
                    "*"
                    (Analysis.Normed.Group.Basic.«term‖_‖»
                     "‖"
                     (Algebra.Group.Defs.«term_•_» `t " • " `x)
                     "‖")))
                  ":="
                  (Term.app `ContinuousLinearMap.le_op_norm [(Term.hole "_") (Term.hole "_")]))
                 (calcStep
                  («term_=_»
                   (Term.hole "_")
                   "="
                   («term_*_»
                    (Analysis.Normed.Group.Basic.«term‖_‖» "‖" `fr "‖")
                    "*"
                    («term_*_»
                     (Analysis.Normed.Group.Basic.«term‖_‖» "‖" `t "‖")
                     "*"
                     (Analysis.Normed.Group.Basic.«term‖_‖» "‖" `x "‖"))))
                  ":="
                  (Term.byTactic
                   "by"
                   (Tactic.tacticSeq
                    (Tactic.tacticSeq1Indented
                     [(Tactic.rwSeq
                       "rw"
                       []
                       (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `norm_smul)] "]")
                       [])]))))
                 (calcStep
                  («term_≤_»
                   (Term.hole "_")
                   "≤"
                   («term_*_»
                    (Analysis.Normed.Group.Basic.«term‖_‖» "‖" `fr "‖")
                    "*"
                    (Analysis.Normed.Group.Basic.«term‖_‖» "‖" `x "‖")))
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
                        [(Tactic.rwRule [] `norm_eq_abs)
                         ","
                         (Tactic.rwRule [] `ht)
                         ","
                         (Tactic.rwRule [] `one_mul)]
                        "]")
                       [])]))))])])))])))
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
         [(Tactic.tacticLet_
           "let"
           (Term.letDecl
            (Term.letIdDecl
             `lm
             []
             [(Term.typeSpec ":" (Algebra.Module.LinearMap.«term_→ₗ[_]_» `F " →ₗ[" `𝕜 "] " `𝕜))]
             ":="
             `fr.to_linear_map.extend_to_𝕜')))
          []
          (Mathlib.Tactic.tacticClassical_
           "classical"
           (Tactic.tacticSeq
            (Tactic.tacticSeq1Indented
             [(Classical.«tacticBy_cases_:_»
               "by_cases"
               [`h ":"]
               («term_=_» (Term.app `lm [`x]) "=" (num "0")))
              []
              (tactic__
               (cdotTk (patternIgnore (token.«· » "·")))
               [(Tactic.rwSeq
                 "rw"
                 []
                 (Tactic.rwRuleSeq
                  "["
                  [(Tactic.rwRule [] `h) "," (Tactic.rwRule [] `norm_zero)]
                  "]")
                 [])
                []
                (Tactic.«tactic_<;>_»
                 (Tactic.apply "apply" `mul_nonneg)
                 "<;>"
                 (Tactic.exact "exact" (Term.app `norm_nonneg [(Term.hole "_")])))])
              []
              (Tactic.tacticLet_
               "let"
               (Term.letDecl (Term.letIdDecl `fx [] [] ":=" («term_⁻¹» (Term.app `lm [`x]) "⁻¹"))))
              []
              (Tactic.tacticLet_
               "let"
               (Term.letDecl
                (Term.letIdDecl
                 `t
                 []
                 []
                 ":="
                 («term_/_»
                  `fx
                  "/"
                  (Term.typeAscription
                   "("
                   (Term.app (Analysis.NormedSpace.Extend.termabs𝕜 "abs𝕜") [`fx])
                   ":"
                   [`𝕜]
                   ")")))))
              []
              (Tactic.tacticHave_
               "have"
               (Term.haveDecl
                (Term.haveIdDecl
                 [`ht []]
                 [(Term.typeSpec
                   ":"
                   («term_=_»
                    (Term.app (Analysis.NormedSpace.Extend.termabs𝕜 "abs𝕜") [`t])
                    "="
                    (num "1")))]
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
                      [(Tactic.simpArgs
                        "["
                        [(Tactic.simpLemma [] [] `abs_of_real)
                         ","
                         (Tactic.simpLemma [] [] `of_real_inv)
                         ","
                         (Tactic.simpLemma [] [] `IsROrC.abs_inv)
                         ","
                         (Tactic.simpLemma [] [] `IsROrC.abs_div)
                         ","
                         (Tactic.simpLemma [] [] `IsROrC.abs_abs)
                         ","
                         (Tactic.simpLemma [] [] `h)]
                        "]")]
                      [])]))))))
              []
              (Tactic.tacticHave_
               "have"
               (Term.haveDecl
                (Term.haveIdDecl
                 [`h1 []]
                 [(Term.typeSpec
                   ":"
                   («term_=_»
                    (Term.typeAscription
                     "("
                     (Term.app `fr [(Algebra.Group.Defs.«term_•_» `t " • " `x)])
                     ":"
                     [`𝕜]
                     ")")
                    "="
                    (Term.app `lm [(Algebra.Group.Defs.«term_•_» `t " • " `x)])))]
                 ":="
                 (Term.byTactic
                  "by"
                  (Tactic.tacticSeq
                   (Tactic.tacticSeq1Indented
                    [(Tactic.apply "apply" `ext)
                     []
                     (tactic__
                      (cdotTk (patternIgnore (token.«· » "·")))
                      [(Tactic.simp
                        "simp"
                        []
                        []
                        ["only"]
                        ["["
                         [(Tactic.simpLemma [] [] `lm)
                          ","
                          (Tactic.simpLemma [] [] `of_real_re)
                          ","
                          (Tactic.simpLemma [] [] `LinearMap.extend_to_𝕜'_apply)
                          ","
                          (Tactic.simpLemma [] [] `mul_re)
                          ","
                          (Tactic.simpLemma [] [] `I_re)
                          ","
                          (Tactic.simpLemma [] [] `of_real_im)
                          ","
                          (Tactic.simpLemma [] [] `zero_mul)
                          ","
                          (Tactic.simpLemma [] [] `AddMonoidHom.map_sub)
                          ","
                          (Tactic.simpLemma [] [] `sub_zero)
                          ","
                          (Tactic.simpLemma [] [] `mul_zero)]
                         "]"]
                        [])
                       []
                       (Tactic.tacticRfl "rfl")])
                     []
                     (tactic__
                      (cdotTk (patternIgnore (token.«· » "·")))
                      [(Mathlib.Tactic.tacticSymm_ "symm" [])
                       []
                       (calcTactic
                        "calc"
                        (calcStep
                         («term_=_»
                          (Term.app
                           `im
                           [(Term.app `lm [(Algebra.Group.Defs.«term_•_» `t " • " `x)])])
                          "="
                          (Term.app `im [(«term_*_» `t "*" (Term.app `lm [`x]))]))
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
                               [(Tactic.rwRule [] `lm.map_smul) "," (Tactic.rwRule [] `smul_eq_mul)]
                               "]")
                              [])]))))
                        [(calcStep
                          («term_=_»
                           (Term.hole "_")
                           "="
                           (Term.app
                            `im
                            [(«term_*_»
                              («term_/_»
                               («term_⁻¹» (Term.app `lm [`x]) "⁻¹")
                               "/"
                               (Term.app
                                (Analysis.NormedSpace.Extend.termabs𝕜 "abs𝕜")
                                [(«term_⁻¹» (Term.app `lm [`x]) "⁻¹")]))
                              "*"
                              (Term.app `lm [`x]))]))
                          ":="
                          `rfl)
                         (calcStep
                          («term_=_»
                           (Term.hole "_")
                           "="
                           (Term.app
                            `im
                            [(«term_/_»
                              (num "1")
                              "/"
                              (Term.typeAscription
                               "("
                               (Term.app
                                (Analysis.NormedSpace.Extend.termabs𝕜 "abs𝕜")
                                [(«term_⁻¹» (Term.app `lm [`x]) "⁻¹")])
                               ":"
                               [`𝕜]
                               ")"))]))
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
                                [(Tactic.rwRule [] `div_mul_eq_mul_div)
                                 ","
                                 (Tactic.rwRule [] (Term.app `inv_mul_cancel [`h]))]
                                "]")
                               [])]))))
                         (calcStep
                          («term_=_» (Term.hole "_") "=" (num "0"))
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
                                [(Tactic.rwRule [(patternIgnore (token.«← » "←"))] `of_real_one)
                                 ","
                                 (Tactic.rwRule [(patternIgnore (token.«← » "←"))] `of_real_div)
                                 ","
                                 (Tactic.rwRule [] `of_real_im)]
                                "]")
                               [])]))))
                         (calcStep
                          («term_=_»
                           (Term.hole "_")
                           "="
                           (Term.app
                            `im
                            [(Term.typeAscription
                              "("
                              (Term.app `fr [(Algebra.Group.Defs.«term_•_» `t " • " `x)])
                              ":"
                              [`𝕜]
                              ")")]))
                          ":="
                          (Term.byTactic
                           "by"
                           (Tactic.tacticSeq
                            (Tactic.tacticSeq1Indented
                             [(Tactic.rwSeq
                               "rw"
                               []
                               (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `of_real_im)] "]")
                               [])]))))])])]))))))
              []
              (calcTactic
               "calc"
               (calcStep
                («term_=_»
                 (Analysis.Normed.Group.Basic.«term‖_‖» "‖" (Term.app `lm [`x]) "‖")
                 "="
                 («term_*_»
                  (Term.app (Analysis.NormedSpace.Extend.termabs𝕜 "abs𝕜") [`t])
                  "*"
                  (Analysis.Normed.Group.Basic.«term‖_‖» "‖" (Term.app `lm [`x]) "‖")))
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
                      [(Tactic.rwRule [] `ht) "," (Tactic.rwRule [] `one_mul)]
                      "]")
                     [])]))))
               [(calcStep
                 («term_=_»
                  (Term.hole "_")
                  "="
                  (Analysis.Normed.Group.Basic.«term‖_‖»
                   "‖"
                   («term_*_» `t "*" (Term.app `lm [`x]))
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
                       [(Tactic.rwRule [(patternIgnore (token.«← » "←"))] `norm_eq_abs)
                        ","
                        (Tactic.rwRule [] `norm_mul)]
                       "]")
                      [])]))))
                (calcStep
                 («term_=_»
                  (Term.hole "_")
                  "="
                  (Analysis.Normed.Group.Basic.«term‖_‖»
                   "‖"
                   (Term.app `lm [(Algebra.Group.Defs.«term_•_» `t " • " `x)])
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
                       [(Tactic.rwRule [(patternIgnore (token.«← » "←"))] `smul_eq_mul)
                        ","
                        (Tactic.rwRule [] `lm.map_smul)]
                       "]")
                      [])]))))
                (calcStep
                 («term_=_»
                  (Term.hole "_")
                  "="
                  (Analysis.Normed.Group.Basic.«term‖_‖»
                   "‖"
                   (Term.typeAscription
                    "("
                    (Term.app `fr [(Algebra.Group.Defs.«term_•_» `t " • " `x)])
                    ":"
                    [`𝕜]
                    ")")
                   "‖"))
                 ":="
                 (Term.byTactic
                  "by"
                  (Tactic.tacticSeq
                   (Tactic.tacticSeq1Indented
                    [(Tactic.rwSeq
                      "rw"
                      []
                      (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `h1)] "]")
                      [])]))))
                (calcStep
                 («term_=_»
                  (Term.hole "_")
                  "="
                  (Analysis.Normed.Group.Basic.«term‖_‖»
                   "‖"
                   (Term.app `fr [(Algebra.Group.Defs.«term_•_» `t " • " `x)])
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
                       [(Tactic.rwRule [] `norm_eq_abs)
                        ","
                        (Tactic.rwRule [] `abs_of_real)
                        ","
                        (Tactic.rwRule [] `norm_eq_abs)
                        ","
                        (Tactic.rwRule [] `abs_to_real)]
                       "]")
                      [])]))))
                (calcStep
                 («term_≤_»
                  (Term.hole "_")
                  "≤"
                  («term_*_»
                   (Analysis.Normed.Group.Basic.«term‖_‖» "‖" `fr "‖")
                   "*"
                   (Analysis.Normed.Group.Basic.«term‖_‖»
                    "‖"
                    (Algebra.Group.Defs.«term_•_» `t " • " `x)
                    "‖")))
                 ":="
                 (Term.app `ContinuousLinearMap.le_op_norm [(Term.hole "_") (Term.hole "_")]))
                (calcStep
                 («term_=_»
                  (Term.hole "_")
                  "="
                  («term_*_»
                   (Analysis.Normed.Group.Basic.«term‖_‖» "‖" `fr "‖")
                   "*"
                   («term_*_»
                    (Analysis.Normed.Group.Basic.«term‖_‖» "‖" `t "‖")
                    "*"
                    (Analysis.Normed.Group.Basic.«term‖_‖» "‖" `x "‖"))))
                 ":="
                 (Term.byTactic
                  "by"
                  (Tactic.tacticSeq
                   (Tactic.tacticSeq1Indented
                    [(Tactic.rwSeq
                      "rw"
                      []
                      (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `norm_smul)] "]")
                      [])]))))
                (calcStep
                 («term_≤_»
                  (Term.hole "_")
                  "≤"
                  («term_*_»
                   (Analysis.Normed.Group.Basic.«term‖_‖» "‖" `fr "‖")
                   "*"
                   (Analysis.Normed.Group.Basic.«term‖_‖» "‖" `x "‖")))
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
                       [(Tactic.rwRule [] `norm_eq_abs)
                        ","
                        (Tactic.rwRule [] `ht)
                        ","
                        (Tactic.rwRule [] `one_mul)]
                       "]")
                      [])]))))])])))])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Mathlib.Tactic.tacticClassical_
       "classical"
       (Tactic.tacticSeq
        (Tactic.tacticSeq1Indented
         [(Classical.«tacticBy_cases_:_»
           "by_cases"
           [`h ":"]
           («term_=_» (Term.app `lm [`x]) "=" (num "0")))
          []
          (tactic__
           (cdotTk (patternIgnore (token.«· » "·")))
           [(Tactic.rwSeq
             "rw"
             []
             (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `h) "," (Tactic.rwRule [] `norm_zero)] "]")
             [])
            []
            (Tactic.«tactic_<;>_»
             (Tactic.apply "apply" `mul_nonneg)
             "<;>"
             (Tactic.exact "exact" (Term.app `norm_nonneg [(Term.hole "_")])))])
          []
          (Tactic.tacticLet_
           "let"
           (Term.letDecl (Term.letIdDecl `fx [] [] ":=" («term_⁻¹» (Term.app `lm [`x]) "⁻¹"))))
          []
          (Tactic.tacticLet_
           "let"
           (Term.letDecl
            (Term.letIdDecl
             `t
             []
             []
             ":="
             («term_/_»
              `fx
              "/"
              (Term.typeAscription
               "("
               (Term.app (Analysis.NormedSpace.Extend.termabs𝕜 "abs𝕜") [`fx])
               ":"
               [`𝕜]
               ")")))))
          []
          (Tactic.tacticHave_
           "have"
           (Term.haveDecl
            (Term.haveIdDecl
             [`ht []]
             [(Term.typeSpec
               ":"
               («term_=_»
                (Term.app (Analysis.NormedSpace.Extend.termabs𝕜 "abs𝕜") [`t])
                "="
                (num "1")))]
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
                  [(Tactic.simpArgs
                    "["
                    [(Tactic.simpLemma [] [] `abs_of_real)
                     ","
                     (Tactic.simpLemma [] [] `of_real_inv)
                     ","
                     (Tactic.simpLemma [] [] `IsROrC.abs_inv)
                     ","
                     (Tactic.simpLemma [] [] `IsROrC.abs_div)
                     ","
                     (Tactic.simpLemma [] [] `IsROrC.abs_abs)
                     ","
                     (Tactic.simpLemma [] [] `h)]
                    "]")]
                  [])]))))))
          []
          (Tactic.tacticHave_
           "have"
           (Term.haveDecl
            (Term.haveIdDecl
             [`h1 []]
             [(Term.typeSpec
               ":"
               («term_=_»
                (Term.typeAscription
                 "("
                 (Term.app `fr [(Algebra.Group.Defs.«term_•_» `t " • " `x)])
                 ":"
                 [`𝕜]
                 ")")
                "="
                (Term.app `lm [(Algebra.Group.Defs.«term_•_» `t " • " `x)])))]
             ":="
             (Term.byTactic
              "by"
              (Tactic.tacticSeq
               (Tactic.tacticSeq1Indented
                [(Tactic.apply "apply" `ext)
                 []
                 (tactic__
                  (cdotTk (patternIgnore (token.«· » "·")))
                  [(Tactic.simp
                    "simp"
                    []
                    []
                    ["only"]
                    ["["
                     [(Tactic.simpLemma [] [] `lm)
                      ","
                      (Tactic.simpLemma [] [] `of_real_re)
                      ","
                      (Tactic.simpLemma [] [] `LinearMap.extend_to_𝕜'_apply)
                      ","
                      (Tactic.simpLemma [] [] `mul_re)
                      ","
                      (Tactic.simpLemma [] [] `I_re)
                      ","
                      (Tactic.simpLemma [] [] `of_real_im)
                      ","
                      (Tactic.simpLemma [] [] `zero_mul)
                      ","
                      (Tactic.simpLemma [] [] `AddMonoidHom.map_sub)
                      ","
                      (Tactic.simpLemma [] [] `sub_zero)
                      ","
                      (Tactic.simpLemma [] [] `mul_zero)]
                     "]"]
                    [])
                   []
                   (Tactic.tacticRfl "rfl")])
                 []
                 (tactic__
                  (cdotTk (patternIgnore (token.«· » "·")))
                  [(Mathlib.Tactic.tacticSymm_ "symm" [])
                   []
                   (calcTactic
                    "calc"
                    (calcStep
                     («term_=_»
                      (Term.app `im [(Term.app `lm [(Algebra.Group.Defs.«term_•_» `t " • " `x)])])
                      "="
                      (Term.app `im [(«term_*_» `t "*" (Term.app `lm [`x]))]))
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
                           [(Tactic.rwRule [] `lm.map_smul) "," (Tactic.rwRule [] `smul_eq_mul)]
                           "]")
                          [])]))))
                    [(calcStep
                      («term_=_»
                       (Term.hole "_")
                       "="
                       (Term.app
                        `im
                        [(«term_*_»
                          («term_/_»
                           («term_⁻¹» (Term.app `lm [`x]) "⁻¹")
                           "/"
                           (Term.app
                            (Analysis.NormedSpace.Extend.termabs𝕜 "abs𝕜")
                            [(«term_⁻¹» (Term.app `lm [`x]) "⁻¹")]))
                          "*"
                          (Term.app `lm [`x]))]))
                      ":="
                      `rfl)
                     (calcStep
                      («term_=_»
                       (Term.hole "_")
                       "="
                       (Term.app
                        `im
                        [(«term_/_»
                          (num "1")
                          "/"
                          (Term.typeAscription
                           "("
                           (Term.app
                            (Analysis.NormedSpace.Extend.termabs𝕜 "abs𝕜")
                            [(«term_⁻¹» (Term.app `lm [`x]) "⁻¹")])
                           ":"
                           [`𝕜]
                           ")"))]))
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
                            [(Tactic.rwRule [] `div_mul_eq_mul_div)
                             ","
                             (Tactic.rwRule [] (Term.app `inv_mul_cancel [`h]))]
                            "]")
                           [])]))))
                     (calcStep
                      («term_=_» (Term.hole "_") "=" (num "0"))
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
                            [(Tactic.rwRule [(patternIgnore (token.«← » "←"))] `of_real_one)
                             ","
                             (Tactic.rwRule [(patternIgnore (token.«← » "←"))] `of_real_div)
                             ","
                             (Tactic.rwRule [] `of_real_im)]
                            "]")
                           [])]))))
                     (calcStep
                      («term_=_»
                       (Term.hole "_")
                       "="
                       (Term.app
                        `im
                        [(Term.typeAscription
                          "("
                          (Term.app `fr [(Algebra.Group.Defs.«term_•_» `t " • " `x)])
                          ":"
                          [`𝕜]
                          ")")]))
                      ":="
                      (Term.byTactic
                       "by"
                       (Tactic.tacticSeq
                        (Tactic.tacticSeq1Indented
                         [(Tactic.rwSeq
                           "rw"
                           []
                           (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `of_real_im)] "]")
                           [])]))))])])]))))))
          []
          (calcTactic
           "calc"
           (calcStep
            («term_=_»
             (Analysis.Normed.Group.Basic.«term‖_‖» "‖" (Term.app `lm [`x]) "‖")
             "="
             («term_*_»
              (Term.app (Analysis.NormedSpace.Extend.termabs𝕜 "abs𝕜") [`t])
              "*"
              (Analysis.Normed.Group.Basic.«term‖_‖» "‖" (Term.app `lm [`x]) "‖")))
            ":="
            (Term.byTactic
             "by"
             (Tactic.tacticSeq
              (Tactic.tacticSeq1Indented
               [(Tactic.rwSeq
                 "rw"
                 []
                 (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `ht) "," (Tactic.rwRule [] `one_mul)] "]")
                 [])]))))
           [(calcStep
             («term_=_»
              (Term.hole "_")
              "="
              (Analysis.Normed.Group.Basic.«term‖_‖»
               "‖"
               («term_*_» `t "*" (Term.app `lm [`x]))
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
                   [(Tactic.rwRule [(patternIgnore (token.«← » "←"))] `norm_eq_abs)
                    ","
                    (Tactic.rwRule [] `norm_mul)]
                   "]")
                  [])]))))
            (calcStep
             («term_=_»
              (Term.hole "_")
              "="
              (Analysis.Normed.Group.Basic.«term‖_‖»
               "‖"
               (Term.app `lm [(Algebra.Group.Defs.«term_•_» `t " • " `x)])
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
                   [(Tactic.rwRule [(patternIgnore (token.«← » "←"))] `smul_eq_mul)
                    ","
                    (Tactic.rwRule [] `lm.map_smul)]
                   "]")
                  [])]))))
            (calcStep
             («term_=_»
              (Term.hole "_")
              "="
              (Analysis.Normed.Group.Basic.«term‖_‖»
               "‖"
               (Term.typeAscription
                "("
                (Term.app `fr [(Algebra.Group.Defs.«term_•_» `t " • " `x)])
                ":"
                [`𝕜]
                ")")
               "‖"))
             ":="
             (Term.byTactic
              "by"
              (Tactic.tacticSeq
               (Tactic.tacticSeq1Indented
                [(Tactic.rwSeq "rw" [] (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `h1)] "]") [])]))))
            (calcStep
             («term_=_»
              (Term.hole "_")
              "="
              (Analysis.Normed.Group.Basic.«term‖_‖»
               "‖"
               (Term.app `fr [(Algebra.Group.Defs.«term_•_» `t " • " `x)])
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
                   [(Tactic.rwRule [] `norm_eq_abs)
                    ","
                    (Tactic.rwRule [] `abs_of_real)
                    ","
                    (Tactic.rwRule [] `norm_eq_abs)
                    ","
                    (Tactic.rwRule [] `abs_to_real)]
                   "]")
                  [])]))))
            (calcStep
             («term_≤_»
              (Term.hole "_")
              "≤"
              («term_*_»
               (Analysis.Normed.Group.Basic.«term‖_‖» "‖" `fr "‖")
               "*"
               (Analysis.Normed.Group.Basic.«term‖_‖»
                "‖"
                (Algebra.Group.Defs.«term_•_» `t " • " `x)
                "‖")))
             ":="
             (Term.app `ContinuousLinearMap.le_op_norm [(Term.hole "_") (Term.hole "_")]))
            (calcStep
             («term_=_»
              (Term.hole "_")
              "="
              («term_*_»
               (Analysis.Normed.Group.Basic.«term‖_‖» "‖" `fr "‖")
               "*"
               («term_*_»
                (Analysis.Normed.Group.Basic.«term‖_‖» "‖" `t "‖")
                "*"
                (Analysis.Normed.Group.Basic.«term‖_‖» "‖" `x "‖"))))
             ":="
             (Term.byTactic
              "by"
              (Tactic.tacticSeq
               (Tactic.tacticSeq1Indented
                [(Tactic.rwSeq
                  "rw"
                  []
                  (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `norm_smul)] "]")
                  [])]))))
            (calcStep
             («term_≤_»
              (Term.hole "_")
              "≤"
              («term_*_»
               (Analysis.Normed.Group.Basic.«term‖_‖» "‖" `fr "‖")
               "*"
               (Analysis.Normed.Group.Basic.«term‖_‖» "‖" `x "‖")))
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
                   [(Tactic.rwRule [] `norm_eq_abs)
                    ","
                    (Tactic.rwRule [] `ht)
                    ","
                    (Tactic.rwRule [] `one_mul)]
                   "]")
                  [])]))))])])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (calcTactic
       "calc"
       (calcStep
        («term_=_»
         (Analysis.Normed.Group.Basic.«term‖_‖» "‖" (Term.app `lm [`x]) "‖")
         "="
         («term_*_»
          (Term.app (Analysis.NormedSpace.Extend.termabs𝕜 "abs𝕜") [`t])
          "*"
          (Analysis.Normed.Group.Basic.«term‖_‖» "‖" (Term.app `lm [`x]) "‖")))
        ":="
        (Term.byTactic
         "by"
         (Tactic.tacticSeq
          (Tactic.tacticSeq1Indented
           [(Tactic.rwSeq
             "rw"
             []
             (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `ht) "," (Tactic.rwRule [] `one_mul)] "]")
             [])]))))
       [(calcStep
         («term_=_»
          (Term.hole "_")
          "="
          (Analysis.Normed.Group.Basic.«term‖_‖» "‖" («term_*_» `t "*" (Term.app `lm [`x])) "‖"))
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
               [(Tactic.rwRule [(patternIgnore (token.«← » "←"))] `norm_eq_abs)
                ","
                (Tactic.rwRule [] `norm_mul)]
               "]")
              [])]))))
        (calcStep
         («term_=_»
          (Term.hole "_")
          "="
          (Analysis.Normed.Group.Basic.«term‖_‖»
           "‖"
           (Term.app `lm [(Algebra.Group.Defs.«term_•_» `t " • " `x)])
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
               [(Tactic.rwRule [(patternIgnore (token.«← » "←"))] `smul_eq_mul)
                ","
                (Tactic.rwRule [] `lm.map_smul)]
               "]")
              [])]))))
        (calcStep
         («term_=_»
          (Term.hole "_")
          "="
          (Analysis.Normed.Group.Basic.«term‖_‖»
           "‖"
           (Term.typeAscription
            "("
            (Term.app `fr [(Algebra.Group.Defs.«term_•_» `t " • " `x)])
            ":"
            [`𝕜]
            ")")
           "‖"))
         ":="
         (Term.byTactic
          "by"
          (Tactic.tacticSeq
           (Tactic.tacticSeq1Indented
            [(Tactic.rwSeq "rw" [] (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `h1)] "]") [])]))))
        (calcStep
         («term_=_»
          (Term.hole "_")
          "="
          (Analysis.Normed.Group.Basic.«term‖_‖»
           "‖"
           (Term.app `fr [(Algebra.Group.Defs.«term_•_» `t " • " `x)])
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
               [(Tactic.rwRule [] `norm_eq_abs)
                ","
                (Tactic.rwRule [] `abs_of_real)
                ","
                (Tactic.rwRule [] `norm_eq_abs)
                ","
                (Tactic.rwRule [] `abs_to_real)]
               "]")
              [])]))))
        (calcStep
         («term_≤_»
          (Term.hole "_")
          "≤"
          («term_*_»
           (Analysis.Normed.Group.Basic.«term‖_‖» "‖" `fr "‖")
           "*"
           (Analysis.Normed.Group.Basic.«term‖_‖»
            "‖"
            (Algebra.Group.Defs.«term_•_» `t " • " `x)
            "‖")))
         ":="
         (Term.app `ContinuousLinearMap.le_op_norm [(Term.hole "_") (Term.hole "_")]))
        (calcStep
         («term_=_»
          (Term.hole "_")
          "="
          («term_*_»
           (Analysis.Normed.Group.Basic.«term‖_‖» "‖" `fr "‖")
           "*"
           («term_*_»
            (Analysis.Normed.Group.Basic.«term‖_‖» "‖" `t "‖")
            "*"
            (Analysis.Normed.Group.Basic.«term‖_‖» "‖" `x "‖"))))
         ":="
         (Term.byTactic
          "by"
          (Tactic.tacticSeq
           (Tactic.tacticSeq1Indented
            [(Tactic.rwSeq
              "rw"
              []
              (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `norm_smul)] "]")
              [])]))))
        (calcStep
         («term_≤_»
          (Term.hole "_")
          "≤"
          («term_*_»
           (Analysis.Normed.Group.Basic.«term‖_‖» "‖" `fr "‖")
           "*"
           (Analysis.Normed.Group.Basic.«term‖_‖» "‖" `x "‖")))
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
               [(Tactic.rwRule [] `norm_eq_abs)
                ","
                (Tactic.rwRule [] `ht)
                ","
                (Tactic.rwRule [] `one_mul)]
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
            [(Tactic.rwRule [] `norm_eq_abs)
             ","
             (Tactic.rwRule [] `ht)
             ","
             (Tactic.rwRule [] `one_mul)]
            "]")
           [])])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.rwSeq
       "rw"
       []
       (Tactic.rwRuleSeq
        "["
        [(Tactic.rwRule [] `norm_eq_abs) "," (Tactic.rwRule [] `ht) "," (Tactic.rwRule [] `one_mul)]
        "]")
       [])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `one_mul
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `ht
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `norm_eq_abs
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, tactic) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_≤_»
       (Term.hole "_")
       "≤"
       («term_*_»
        (Analysis.Normed.Group.Basic.«term‖_‖» "‖" `fr "‖")
        "*"
        (Analysis.Normed.Group.Basic.«term‖_‖» "‖" `x "‖")))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_*_»
       (Analysis.Normed.Group.Basic.«term‖_‖» "‖" `fr "‖")
       "*"
       (Analysis.Normed.Group.Basic.«term‖_‖» "‖" `x "‖"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Analysis.Normed.Group.Basic.«term‖_‖» "‖" `x "‖")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `x
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 71 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 70, term))
      (Analysis.Normed.Group.Basic.«term‖_‖» "‖" `fr "‖")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `fr
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
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
         [(Tactic.rwSeq "rw" [] (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `norm_smul)] "]") [])])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.rwSeq "rw" [] (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `norm_smul)] "]") [])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `norm_smul
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, tactic) <=? (none, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_=_»
       (Term.hole "_")
       "="
       («term_*_»
        (Analysis.Normed.Group.Basic.«term‖_‖» "‖" `fr "‖")
        "*"
        («term_*_»
         (Analysis.Normed.Group.Basic.«term‖_‖» "‖" `t "‖")
         "*"
         (Analysis.Normed.Group.Basic.«term‖_‖» "‖" `x "‖"))))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_*_»
       (Analysis.Normed.Group.Basic.«term‖_‖» "‖" `fr "‖")
       "*"
       («term_*_»
        (Analysis.Normed.Group.Basic.«term‖_‖» "‖" `t "‖")
        "*"
        (Analysis.Normed.Group.Basic.«term‖_‖» "‖" `x "‖")))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_*_»
       (Analysis.Normed.Group.Basic.«term‖_‖» "‖" `t "‖")
       "*"
       (Analysis.Normed.Group.Basic.«term‖_‖» "‖" `x "‖"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Analysis.Normed.Group.Basic.«term‖_‖» "‖" `x "‖")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `x
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 71 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 70, term))
      (Analysis.Normed.Group.Basic.«term‖_‖» "‖" `t "‖")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `t
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 70 >? 1024, (none, [anonymous]) <=? (some 70, term)
[PrettyPrinter.parenthesize] ...precedences are 71 >? 70, (some 71, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     («term_*_»
      (Analysis.Normed.Group.Basic.«term‖_‖» "‖" `t "‖")
      "*"
      (Analysis.Normed.Group.Basic.«term‖_‖» "‖" `x "‖"))
     ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 70, term))
      (Analysis.Normed.Group.Basic.«term‖_‖» "‖" `fr "‖")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `fr
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 70 >? 1024, (none, [anonymous]) <=? (some 70, term)
[PrettyPrinter.parenthesize] ...precedences are 51 >? 70, (some 71, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 50, term))
      (Term.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1024, (none, [anonymous]) <=? (some 50, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 50, (some 51, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, term))
      (Term.app `ContinuousLinearMap.le_op_norm [(Term.hole "_") (Term.hole "_")])
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
      `ContinuousLinearMap.le_op_norm
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_≤_»
       (Term.hole "_")
       "≤"
       («term_*_»
        (Analysis.Normed.Group.Basic.«term‖_‖» "‖" `fr "‖")
        "*"
        (Analysis.Normed.Group.Basic.«term‖_‖» "‖" (Algebra.Group.Defs.«term_•_» `t " • " `x) "‖")))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_*_»
       (Analysis.Normed.Group.Basic.«term‖_‖» "‖" `fr "‖")
       "*"
       (Analysis.Normed.Group.Basic.«term‖_‖» "‖" (Algebra.Group.Defs.«term_•_» `t " • " `x) "‖"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Analysis.Normed.Group.Basic.«term‖_‖» "‖" (Algebra.Group.Defs.«term_•_» `t " • " `x) "‖")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Algebra.Group.Defs.«term_•_» `t " • " `x)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `x
[PrettyPrinter.parenthesize] ...precedences are 73 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 73, term))
      `t
[PrettyPrinter.parenthesize] ...precedences are 74 >? 1024, (none, [anonymous]) <=? (some 73, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 73, (some 73, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 71 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 70, term))
      (Analysis.Normed.Group.Basic.«term‖_‖» "‖" `fr "‖")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `fr
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
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
         [(Tactic.rwSeq
           "rw"
           []
           (Tactic.rwRuleSeq
            "["
            [(Tactic.rwRule [] `norm_eq_abs)
             ","
             (Tactic.rwRule [] `abs_of_real)
             ","
             (Tactic.rwRule [] `norm_eq_abs)
             ","
             (Tactic.rwRule [] `abs_to_real)]
            "]")
           [])])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.rwSeq
       "rw"
       []
       (Tactic.rwRuleSeq
        "["
        [(Tactic.rwRule [] `norm_eq_abs)
         ","
         (Tactic.rwRule [] `abs_of_real)
         ","
         (Tactic.rwRule [] `norm_eq_abs)
         ","
         (Tactic.rwRule [] `abs_to_real)]
        "]")
       [])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `abs_to_real
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `norm_eq_abs
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `abs_of_real
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `norm_eq_abs
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, tactic) <=? (none, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_=_»
       (Term.hole "_")
       "="
       (Analysis.Normed.Group.Basic.«term‖_‖»
        "‖"
        (Term.app `fr [(Algebra.Group.Defs.«term_•_» `t " • " `x)])
        "‖"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Analysis.Normed.Group.Basic.«term‖_‖»
       "‖"
       (Term.app `fr [(Algebra.Group.Defs.«term_•_» `t " • " `x)])
       "‖")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `fr [(Algebra.Group.Defs.«term_•_» `t " • " `x)])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Algebra.Group.Defs.«term_•_»', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Algebra.Group.Defs.«term_•_»', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Algebra.Group.Defs.«term_•_» `t " • " `x)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `x
[PrettyPrinter.parenthesize] ...precedences are 73 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 73, term))
      `t
[PrettyPrinter.parenthesize] ...precedences are 74 >? 1024, (none, [anonymous]) <=? (some 73, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 73, (some 73, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Algebra.Group.Defs.«term_•_» `t " • " `x)
     ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `fr
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 50, term))
      (Term.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1024, (none, [anonymous]) <=? (some 50, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 50, (some 51, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, term))
      (Term.byTactic
       "by"
       (Tactic.tacticSeq
        (Tactic.tacticSeq1Indented
         [(Tactic.rwSeq "rw" [] (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `h1)] "]") [])])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.rwSeq "rw" [] (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `h1)] "]") [])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `h1
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, tactic) <=? (none, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_=_»
       (Term.hole "_")
       "="
       (Analysis.Normed.Group.Basic.«term‖_‖»
        "‖"
        (Term.typeAscription
         "("
         (Term.app `fr [(Algebra.Group.Defs.«term_•_» `t " • " `x)])
         ":"
         [`𝕜]
         ")")
        "‖"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Analysis.Normed.Group.Basic.«term‖_‖»
       "‖"
       (Term.typeAscription
        "("
        (Term.app `fr [(Algebra.Group.Defs.«term_•_» `t " • " `x)])
        ":"
        [`𝕜]
        ")")
       "‖")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.typeAscription
       "("
       (Term.app `fr [(Algebra.Group.Defs.«term_•_» `t " • " `x)])
       ":"
       [`𝕜]
       ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `𝕜
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `fr [(Algebra.Group.Defs.«term_•_» `t " • " `x)])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Algebra.Group.Defs.«term_•_»', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Algebra.Group.Defs.«term_•_»', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Algebra.Group.Defs.«term_•_» `t " • " `x)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `x
[PrettyPrinter.parenthesize] ...precedences are 73 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 73, term))
      `t
[PrettyPrinter.parenthesize] ...precedences are 74 >? 1024, (none, [anonymous]) <=? (some 73, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 73, (some 73, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Algebra.Group.Defs.«term_•_» `t " • " `x)
     ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `fr
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 50, term))
      (Term.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1024, (none, [anonymous]) <=? (some 50, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 50, (some 51, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, term))
      (Term.byTactic
       "by"
       (Tactic.tacticSeq
        (Tactic.tacticSeq1Indented
         [(Tactic.rwSeq
           "rw"
           []
           (Tactic.rwRuleSeq
            "["
            [(Tactic.rwRule [(patternIgnore (token.«← » "←"))] `smul_eq_mul)
             ","
             (Tactic.rwRule [] `lm.map_smul)]
            "]")
           [])])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.rwSeq
       "rw"
       []
       (Tactic.rwRuleSeq
        "["
        [(Tactic.rwRule [(patternIgnore (token.«← » "←"))] `smul_eq_mul)
         ","
         (Tactic.rwRule [] `lm.map_smul)]
        "]")
       [])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `lm.map_smul
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `smul_eq_mul
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, tactic) <=? (none, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_=_»
       (Term.hole "_")
       "="
       (Analysis.Normed.Group.Basic.«term‖_‖»
        "‖"
        (Term.app `lm [(Algebra.Group.Defs.«term_•_» `t " • " `x)])
        "‖"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Analysis.Normed.Group.Basic.«term‖_‖»
       "‖"
       (Term.app `lm [(Algebra.Group.Defs.«term_•_» `t " • " `x)])
       "‖")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `lm [(Algebra.Group.Defs.«term_•_» `t " • " `x)])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Algebra.Group.Defs.«term_•_»', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Algebra.Group.Defs.«term_•_»', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Algebra.Group.Defs.«term_•_» `t " • " `x)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `x
[PrettyPrinter.parenthesize] ...precedences are 73 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 73, term))
      `t
[PrettyPrinter.parenthesize] ...precedences are 74 >? 1024, (none, [anonymous]) <=? (some 73, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 73, (some 73, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Algebra.Group.Defs.«term_•_» `t " • " `x)
     ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `lm
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 50, term))
      (Term.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1024, (none, [anonymous]) <=? (some 50, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 50, (some 51, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, term))
      (Term.byTactic
       "by"
       (Tactic.tacticSeq
        (Tactic.tacticSeq1Indented
         [(Tactic.rwSeq
           "rw"
           []
           (Tactic.rwRuleSeq
            "["
            [(Tactic.rwRule [(patternIgnore (token.«← » "←"))] `norm_eq_abs)
             ","
             (Tactic.rwRule [] `norm_mul)]
            "]")
           [])])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.rwSeq
       "rw"
       []
       (Tactic.rwRuleSeq
        "["
        [(Tactic.rwRule [(patternIgnore (token.«← » "←"))] `norm_eq_abs)
         ","
         (Tactic.rwRule [] `norm_mul)]
        "]")
       [])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `norm_mul
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `norm_eq_abs
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, tactic) <=? (none, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_=_»
       (Term.hole "_")
       "="
       (Analysis.Normed.Group.Basic.«term‖_‖» "‖" («term_*_» `t "*" (Term.app `lm [`x])) "‖"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Analysis.Normed.Group.Basic.«term‖_‖» "‖" («term_*_» `t "*" (Term.app `lm [`x])) "‖")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_*_» `t "*" (Term.app `lm [`x]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `lm [`x])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `x
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `lm
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 71 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 70, term))
      `t
[PrettyPrinter.parenthesize] ...precedences are 70 >? 1024, (none, [anonymous]) <=? (some 70, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 70, (some 71, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 50, term))
      (Term.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1024, (none, [anonymous]) <=? (some 50, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 50, (some 51, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, term))
      (Term.byTactic
       "by"
       (Tactic.tacticSeq
        (Tactic.tacticSeq1Indented
         [(Tactic.rwSeq
           "rw"
           []
           (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `ht) "," (Tactic.rwRule [] `one_mul)] "]")
           [])])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.rwSeq
       "rw"
       []
       (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `ht) "," (Tactic.rwRule [] `one_mul)] "]")
       [])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `one_mul
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `ht
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, tactic) <=? (none, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_=_»
       (Analysis.Normed.Group.Basic.«term‖_‖» "‖" (Term.app `lm [`x]) "‖")
       "="
       («term_*_»
        (Term.app (Analysis.NormedSpace.Extend.termabs𝕜 "abs𝕜") [`t])
        "*"
        (Analysis.Normed.Group.Basic.«term‖_‖» "‖" (Term.app `lm [`x]) "‖")))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_*_»
       (Term.app (Analysis.NormedSpace.Extend.termabs𝕜 "abs𝕜") [`t])
       "*"
       (Analysis.Normed.Group.Basic.«term‖_‖» "‖" (Term.app `lm [`x]) "‖"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Analysis.Normed.Group.Basic.«term‖_‖» "‖" (Term.app `lm [`x]) "‖")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `lm [`x])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `x
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `lm
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 71 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 70, term))
      (Term.app (Analysis.NormedSpace.Extend.termabs𝕜 "abs𝕜") [`t])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `t
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (Analysis.NormedSpace.Extend.termabs𝕜 "abs𝕜")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Analysis.NormedSpace.Extend.termabs𝕜', expected 'Analysis.NormedSpace.Extend.termabs𝕜._@.Analysis.NormedSpace.Extend._hyg.6'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.declValSimple', expected 'Lean.Parser.Command.declValEqns'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.declValSimple', expected 'Lean.Parser.Command.whereStructInst'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.opaque'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.instance'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.axiom'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.example'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.inductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.classInductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.structure'-/-- failed to format: format: uncaught backtrack exception
/-- The norm of the extension is bounded by `‖fr‖`. -/
  theorem
    norm_bound
    [ NormedSpace ℝ F ] [ IsScalarTower ℝ 𝕜 F ] ( fr : F →L[ ℝ ] ℝ ) ( x : F )
      : ‖ ( fr . toLinearMap . extendTo𝕜' x : 𝕜 ) ‖ ≤ ‖ fr ‖ * ‖ x ‖
    :=
      by
        let lm : F →ₗ[ 𝕜 ] 𝕜 := fr.to_linear_map.extend_to_𝕜'
          classical
            by_cases h : lm x = 0
              · rw [ h , norm_zero ] apply mul_nonneg <;> exact norm_nonneg _
              let fx := lm x ⁻¹
              let t := fx / ( abs𝕜 fx : 𝕜 )
              have
                ht
                  : abs𝕜 t = 1
                  :=
                  by
                    field_simp
                      [
                        abs_of_real
                          ,
                          of_real_inv
                          ,
                          IsROrC.abs_inv
                          ,
                          IsROrC.abs_div
                          ,
                          IsROrC.abs_abs
                          ,
                          h
                        ]
              have
                h1
                  : ( fr t • x : 𝕜 ) = lm t • x
                  :=
                  by
                    apply ext
                      ·
                        simp
                            only
                            [
                              lm
                                ,
                                of_real_re
                                ,
                                LinearMap.extend_to_𝕜'_apply
                                ,
                                mul_re
                                ,
                                I_re
                                ,
                                of_real_im
                                ,
                                zero_mul
                                ,
                                AddMonoidHom.map_sub
                                ,
                                sub_zero
                                ,
                                mul_zero
                              ]
                          rfl
                      ·
                        symm
                          calc
                            im lm t • x = im t * lm x := by rw [ lm.map_smul , smul_eq_mul ]
                            _ = im lm x ⁻¹ / abs𝕜 lm x ⁻¹ * lm x := rfl
                              _ = im 1 / ( abs𝕜 lm x ⁻¹ : 𝕜 )
                                :=
                                by rw [ div_mul_eq_mul_div , inv_mul_cancel h ]
                              _ = 0 := by rw [ ← of_real_one , ← of_real_div , of_real_im ]
                              _ = im ( fr t • x : 𝕜 ) := by rw [ of_real_im ]
              calc
                ‖ lm x ‖ = abs𝕜 t * ‖ lm x ‖ := by rw [ ht , one_mul ]
                _ = ‖ t * lm x ‖ := by rw [ ← norm_eq_abs , norm_mul ]
                  _ = ‖ lm t • x ‖ := by rw [ ← smul_eq_mul , lm.map_smul ]
                  _ = ‖ ( fr t • x : 𝕜 ) ‖ := by rw [ h1 ]
                  _ = ‖ fr t • x ‖
                    :=
                    by rw [ norm_eq_abs , abs_of_real , norm_eq_abs , abs_to_real ]
                  _ ≤ ‖ fr ‖ * ‖ t • x ‖ := ContinuousLinearMap.le_op_norm _ _
                  _ = ‖ fr ‖ * ‖ t ‖ * ‖ x ‖ := by rw [ norm_smul ]
                  _ ≤ ‖ fr ‖ * ‖ x ‖ := by rw [ norm_eq_abs , ht , one_mul ]
#align norm_bound norm_bound

/-- Extend `fr : F →L[ℝ] ℝ` to `F →L[𝕜] 𝕜`. -/
noncomputable def ContinuousLinearMap.extendTo𝕜' [NormedSpace ℝ F] [IsScalarTower ℝ 𝕜 F]
    (fr : F →L[ℝ] ℝ) : F →L[𝕜] 𝕜 :=
  LinearMap.mkContinuous _ ‖fr‖ (norm_bound _)
#align continuous_linear_map.extend_to_𝕜' ContinuousLinearMap.extendTo𝕜'

theorem ContinuousLinearMap.extend_to_𝕜'_apply [NormedSpace ℝ F] [IsScalarTower ℝ 𝕜 F]
    (fr : F →L[ℝ] ℝ) (x : F) : fr.extendTo𝕜' x = (fr x : 𝕜) - (i : 𝕜) * fr ((i : 𝕜) • x) :=
  rfl
#align continuous_linear_map.extend_to_𝕜'_apply ContinuousLinearMap.extend_to_𝕜'_apply

/-- Extend `fr : restrict_scalars ℝ 𝕜 F →ₗ[ℝ] ℝ` to `F →ₗ[𝕜] 𝕜`. -/
noncomputable def LinearMap.extendTo𝕜 (fr : RestrictScalars ℝ 𝕜 F →ₗ[ℝ] ℝ) : F →ₗ[𝕜] 𝕜 :=
  fr.extendTo𝕜'
#align linear_map.extend_to_𝕜 LinearMap.extendTo𝕜

theorem LinearMap.extend_to_𝕜_apply (fr : RestrictScalars ℝ 𝕜 F →ₗ[ℝ] ℝ) (x : F) :
    fr.extendTo𝕜 x = (fr x : 𝕜) - (i : 𝕜) * fr ((i : 𝕜) • x : _) :=
  rfl
#align linear_map.extend_to_𝕜_apply LinearMap.extend_to_𝕜_apply

/-- Extend `fr : restrict_scalars ℝ 𝕜 F →L[ℝ] ℝ` to `F →L[𝕜] 𝕜`. -/
noncomputable def ContinuousLinearMap.extendTo𝕜 (fr : RestrictScalars ℝ 𝕜 F →L[ℝ] ℝ) : F →L[𝕜] 𝕜 :=
  fr.extendTo𝕜'
#align continuous_linear_map.extend_to_𝕜 ContinuousLinearMap.extendTo𝕜

theorem ContinuousLinearMap.extend_to_𝕜_apply (fr : RestrictScalars ℝ 𝕜 F →L[ℝ] ℝ) (x : F) :
    fr.extendTo𝕜 x = (fr x : 𝕜) - (i : 𝕜) * fr ((i : 𝕜) • x : _) :=
  rfl
#align continuous_linear_map.extend_to_𝕜_apply ContinuousLinearMap.extend_to_𝕜_apply

