/-
Copyright (c) 2022 Jireh Loreaux. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jireh Loreaux

! This file was ported from Lean 3 source module analysis.normed_space.star.spectrum
! leanprover-community/mathlib commit 6d0adfa76594f304b4650d098273d4366edeb61b
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Analysis.NormedSpace.Star.Basic
import Mathbin.Analysis.NormedSpace.Spectrum
import Mathbin.Analysis.NormedSpace.Star.Exponential
import Mathbin.Analysis.SpecialFunctions.Exponential
import Mathbin.Algebra.Star.StarAlgHom

/-! # Spectral properties in C⋆-algebras
In this file, we establish various propreties related to the spectrum of elements in C⋆-algebras.
-/


-- mathport name: «expr ⋆»
local postfix:max "⋆" => star

section

open TopologicalSpace Ennreal

open Filter Ennreal spectrum CstarRing

section UnitarySpectrum

variable {𝕜 : Type _} [NormedField 𝕜] {E : Type _} [NormedRing E] [StarRing E] [CstarRing E]
  [NormedAlgebra 𝕜 E] [CompleteSpace E]

theorem unitary.spectrum_subset_circle (u : unitary E) : spectrum 𝕜 (u : E) ⊆ Metric.sphere 0 1 :=
  by
  nontriviality E
  refine' fun k hk => mem_sphere_zero_iff_norm.mpr (le_antisymm _ _)
  · simpa only [CstarRing.norm_coe_unitary u] using norm_le_norm_of_mem hk
  · rw [← unitary.coe_to_units_apply u] at hk
    have hnk := ne_zero_of_mem_of_unit hk
    rw [← inv_inv (unitary.toUnits u), ← spectrum.map_inv, Set.mem_inv] at hk
    have : ‖k‖⁻¹ ≤ ‖↑(unitary.toUnits u)⁻¹‖
    simpa only [norm_inv] using norm_le_norm_of_mem hk
    simpa using inv_le_of_inv_le (norm_pos_iff.mpr hnk) this
#align unitary.spectrum_subset_circle unitary.spectrum_subset_circle

theorem spectrum.subset_circle_of_unitary {u : E} (h : u ∈ unitary E) :
    spectrum 𝕜 u ⊆ Metric.sphere 0 1 :=
  unitary.spectrum_subset_circle ⟨u, h⟩
#align spectrum.subset_circle_of_unitary spectrum.subset_circle_of_unitary

end UnitarySpectrum

section ComplexScalars

open Complex

variable {A : Type _} [NormedRing A] [NormedAlgebra ℂ A] [CompleteSpace A] [StarRing A]
  [CstarRing A]

-- mathport name: «expr↑ₐ»
local notation "↑ₐ" => algebraMap ℂ A

theorem IsSelfAdjoint.spectral_radius_eq_nnnorm {a : A} (ha : IsSelfAdjoint a) :
    spectralRadius ℂ a = ‖a‖₊ :=
  by
  have hconst : tendsto (fun n : ℕ => (‖a‖₊ : ℝ≥0∞)) at_top _ := tendsto_const_nhds
  refine' tendsto_nhds_unique _ hconst
  convert
    (spectrum.pow_nnnorm_pow_one_div_tendsto_nhds_spectral_radius (a : A)).comp
      (Nat.tendsto_pow_at_top_at_top_of_one_lt one_lt_two)
  refine' funext fun n => _
  rw [Function.comp_apply, ha.nnnorm_pow_two_pow, Ennreal.coe_pow, ← rpow_nat_cast, ← rpow_mul]
  simp
#align is_self_adjoint.spectral_radius_eq_nnnorm IsSelfAdjoint.spectral_radius_eq_nnnorm

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers [] [] [] [] [] [])
     (Command.theorem
      "theorem"
      (Command.declId `IsStarNormal.spectral_radius_eq_nnnorm [])
      (Command.declSig
       [(Term.explicitBinder "(" [`a] [":" `A] [] ")")
        (Term.instBinder "[" [] (Term.app `IsStarNormal [`a]) "]")]
       (Term.typeSpec
        ":"
        («term_=_»
         (Term.app `spectralRadius [(Data.Complex.Basic.termℂ "ℂ") `a])
         "="
         (Analysis.Normed.Group.Basic.«term‖_‖₊» "‖" `a "‖₊"))))
      (Command.declValSimple
       ":="
       (Term.byTactic
        "by"
        (Tactic.tacticSeq
         (Tactic.tacticSeq1Indented
          [(Tactic.refine'
            "refine'"
            (Term.app
             (Term.proj (Term.app `Ennreal.pow_strict_mono [`two_ne_zero]) "." `Injective)
             [(Term.hole "_")]))
           []
           (Tactic.tacticHave_
            "have"
            (Term.haveDecl
             (Term.haveIdDecl
              [`heq []]
              [(Term.typeSpec
                ":"
                («term_=_»
                 (Term.fun
                  "fun"
                  (Term.basicFun
                   [`n]
                   [(Term.typeSpec ":" (termℕ "ℕ"))]
                   "=>"
                   (Term.typeAscription
                    "("
                    («term_^_»
                     (Analysis.Normed.Group.Basic.«term‖_‖₊»
                      "‖"
                      («term_^_»
                       («term_*_» (Analysis.NormedSpace.Star.Spectrum.«term_⋆» `a "⋆") "*" `a)
                       "^"
                       `n)
                      "‖₊")
                     "^"
                     (Term.typeAscription
                      "("
                      («term_/_» (num "1") "/" `n)
                      ":"
                      [(Data.Real.Basic.termℝ "ℝ")]
                      ")"))
                    ":"
                    [(Ennreal.Data.Real.Ennreal.ennreal "ℝ≥0∞")]
                    ")")))
                 "="
                 («term_∘_»
                  (Term.fun "fun" (Term.basicFun [`x] [] "=>" («term_^_» `x "^" (num "2"))))
                  "∘"
                  (Term.fun
                   "fun"
                   (Term.basicFun
                    [`n]
                    [(Term.typeSpec ":" (termℕ "ℕ"))]
                    "=>"
                    (Term.typeAscription
                     "("
                     («term_^_»
                      (Analysis.Normed.Group.Basic.«term‖_‖₊» "‖" («term_^_» `a "^" `n) "‖₊")
                      "^"
                      (Term.typeAscription
                       "("
                       («term_/_» (num "1") "/" `n)
                       ":"
                       [(Data.Real.Basic.termℝ "ℝ")]
                       ")"))
                     ":"
                     [(Ennreal.Data.Real.Ennreal.ennreal "ℝ≥0∞")]
                     ")"))))))]
              ":="
              (Term.byTactic
               "by"
               (Tactic.tacticSeq
                (Tactic.tacticSeq1Indented
                 [(tacticFunext__ "funext" [])
                  []
                  (Tactic.rwSeq
                   "rw"
                   []
                   (Tactic.rwRuleSeq
                    "["
                    [(Tactic.rwRule [] `Function.comp_apply)
                     ","
                     (Tactic.rwRule [(patternIgnore (token.«← » "←"))] `rpow_nat_cast)
                     ","
                     (Tactic.rwRule [(patternIgnore (token.«← » "←"))] `rpow_mul)
                     ","
                     (Tactic.rwRule [] `mul_comm)
                     ","
                     (Tactic.rwRule [] `rpow_mul)
                     ","
                     (Tactic.rwRule [] `rpow_nat_cast)
                     ","
                     (Tactic.rwRule [(patternIgnore (token.«← » "←"))] `coe_pow)
                     ","
                     (Tactic.rwRule [] `sq)
                     ","
                     (Tactic.rwRule [(patternIgnore (token.«← » "←"))] `nnnorm_star_mul_self)
                     ","
                     (Tactic.rwRule
                      []
                      (Term.app `Commute.mul_pow [(Term.app `star_comm_self' [`a])]))
                     ","
                     (Tactic.rwRule [] `star_pow)]
                    "]")
                   [])]))))))
           []
           (Tactic.tacticHave_
            "have"
            (Term.haveDecl
             (Term.haveIdDecl
              [`h₂ []]
              []
              ":="
              (Term.app
               (Term.proj
                (Term.app
                 (Term.proj (Term.app `Ennreal.continuous_pow [(num "2")]) "." `Tendsto)
                 [(Term.app `spectralRadius [(Data.Complex.Basic.termℂ "ℂ") `a])])
                "."
                `comp)
               [(Term.app `spectrum.pow_nnnorm_pow_one_div_tendsto_nhds_spectral_radius [`a])]))))
           []
           (Tactic.rwSeq
            "rw"
            []
            (Tactic.rwRuleSeq "[" [(Tactic.rwRule [(patternIgnore (token.«← » "←"))] `HEq)] "]")
            [(Tactic.location "at" (Tactic.locationHyp [`h₂] []))])
           []
           (convert
            "convert"
            []
            (Term.app
             `tendsto_nhds_unique
             [`h₂
              (Term.app
               `pow_nnnorm_pow_one_div_tendsto_nhds_spectral_radius
               [(«term_*_» (Analysis.NormedSpace.Star.Spectrum.«term_⋆» `a "⋆") "*" `a)])])
            [])
           []
           (Tactic.rwSeq
            "rw"
            []
            (Tactic.rwRuleSeq
             "["
             [(Tactic.rwRule
               []
               (Term.proj
                (Term.app `IsSelfAdjoint.star_mul_self [`a])
                "."
                `spectral_radius_eq_nnnorm))
              ","
              (Tactic.rwRule [] `sq)
              ","
              (Tactic.rwRule [] `nnnorm_star_mul_self)
              ","
              (Tactic.rwRule [] `coe_mul)]
             "]")
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
            (Term.proj (Term.app `Ennreal.pow_strict_mono [`two_ne_zero]) "." `Injective)
            [(Term.hole "_")]))
          []
          (Tactic.tacticHave_
           "have"
           (Term.haveDecl
            (Term.haveIdDecl
             [`heq []]
             [(Term.typeSpec
               ":"
               («term_=_»
                (Term.fun
                 "fun"
                 (Term.basicFun
                  [`n]
                  [(Term.typeSpec ":" (termℕ "ℕ"))]
                  "=>"
                  (Term.typeAscription
                   "("
                   («term_^_»
                    (Analysis.Normed.Group.Basic.«term‖_‖₊»
                     "‖"
                     («term_^_»
                      («term_*_» (Analysis.NormedSpace.Star.Spectrum.«term_⋆» `a "⋆") "*" `a)
                      "^"
                      `n)
                     "‖₊")
                    "^"
                    (Term.typeAscription
                     "("
                     («term_/_» (num "1") "/" `n)
                     ":"
                     [(Data.Real.Basic.termℝ "ℝ")]
                     ")"))
                   ":"
                   [(Ennreal.Data.Real.Ennreal.ennreal "ℝ≥0∞")]
                   ")")))
                "="
                («term_∘_»
                 (Term.fun "fun" (Term.basicFun [`x] [] "=>" («term_^_» `x "^" (num "2"))))
                 "∘"
                 (Term.fun
                  "fun"
                  (Term.basicFun
                   [`n]
                   [(Term.typeSpec ":" (termℕ "ℕ"))]
                   "=>"
                   (Term.typeAscription
                    "("
                    («term_^_»
                     (Analysis.Normed.Group.Basic.«term‖_‖₊» "‖" («term_^_» `a "^" `n) "‖₊")
                     "^"
                     (Term.typeAscription
                      "("
                      («term_/_» (num "1") "/" `n)
                      ":"
                      [(Data.Real.Basic.termℝ "ℝ")]
                      ")"))
                    ":"
                    [(Ennreal.Data.Real.Ennreal.ennreal "ℝ≥0∞")]
                    ")"))))))]
             ":="
             (Term.byTactic
              "by"
              (Tactic.tacticSeq
               (Tactic.tacticSeq1Indented
                [(tacticFunext__ "funext" [])
                 []
                 (Tactic.rwSeq
                  "rw"
                  []
                  (Tactic.rwRuleSeq
                   "["
                   [(Tactic.rwRule [] `Function.comp_apply)
                    ","
                    (Tactic.rwRule [(patternIgnore (token.«← » "←"))] `rpow_nat_cast)
                    ","
                    (Tactic.rwRule [(patternIgnore (token.«← » "←"))] `rpow_mul)
                    ","
                    (Tactic.rwRule [] `mul_comm)
                    ","
                    (Tactic.rwRule [] `rpow_mul)
                    ","
                    (Tactic.rwRule [] `rpow_nat_cast)
                    ","
                    (Tactic.rwRule [(patternIgnore (token.«← » "←"))] `coe_pow)
                    ","
                    (Tactic.rwRule [] `sq)
                    ","
                    (Tactic.rwRule [(patternIgnore (token.«← » "←"))] `nnnorm_star_mul_self)
                    ","
                    (Tactic.rwRule
                     []
                     (Term.app `Commute.mul_pow [(Term.app `star_comm_self' [`a])]))
                    ","
                    (Tactic.rwRule [] `star_pow)]
                   "]")
                  [])]))))))
          []
          (Tactic.tacticHave_
           "have"
           (Term.haveDecl
            (Term.haveIdDecl
             [`h₂ []]
             []
             ":="
             (Term.app
              (Term.proj
               (Term.app
                (Term.proj (Term.app `Ennreal.continuous_pow [(num "2")]) "." `Tendsto)
                [(Term.app `spectralRadius [(Data.Complex.Basic.termℂ "ℂ") `a])])
               "."
               `comp)
              [(Term.app `spectrum.pow_nnnorm_pow_one_div_tendsto_nhds_spectral_radius [`a])]))))
          []
          (Tactic.rwSeq
           "rw"
           []
           (Tactic.rwRuleSeq "[" [(Tactic.rwRule [(patternIgnore (token.«← » "←"))] `HEq)] "]")
           [(Tactic.location "at" (Tactic.locationHyp [`h₂] []))])
          []
          (convert
           "convert"
           []
           (Term.app
            `tendsto_nhds_unique
            [`h₂
             (Term.app
              `pow_nnnorm_pow_one_div_tendsto_nhds_spectral_radius
              [(«term_*_» (Analysis.NormedSpace.Star.Spectrum.«term_⋆» `a "⋆") "*" `a)])])
           [])
          []
          (Tactic.rwSeq
           "rw"
           []
           (Tactic.rwRuleSeq
            "["
            [(Tactic.rwRule
              []
              (Term.proj
               (Term.app `IsSelfAdjoint.star_mul_self [`a])
               "."
               `spectral_radius_eq_nnnorm))
             ","
             (Tactic.rwRule [] `sq)
             ","
             (Tactic.rwRule [] `nnnorm_star_mul_self)
             ","
             (Tactic.rwRule [] `coe_mul)]
            "]")
           [])])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.rwSeq
       "rw"
       []
       (Tactic.rwRuleSeq
        "["
        [(Tactic.rwRule
          []
          (Term.proj (Term.app `IsSelfAdjoint.star_mul_self [`a]) "." `spectral_radius_eq_nnnorm))
         ","
         (Tactic.rwRule [] `sq)
         ","
         (Tactic.rwRule [] `nnnorm_star_mul_self)
         ","
         (Tactic.rwRule [] `coe_mul)]
        "]")
       [])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `coe_mul
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `nnnorm_star_mul_self
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `sq
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.proj (Term.app `IsSelfAdjoint.star_mul_self [`a]) "." `spectral_radius_eq_nnnorm)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.app `IsSelfAdjoint.star_mul_self [`a])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `a
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `IsSelfAdjoint.star_mul_self
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.app `IsSelfAdjoint.star_mul_self [`a])
     ")")
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (convert
       "convert"
       []
       (Term.app
        `tendsto_nhds_unique
        [`h₂
         (Term.app
          `pow_nnnorm_pow_one_div_tendsto_nhds_spectral_radius
          [(«term_*_» (Analysis.NormedSpace.Star.Spectrum.«term_⋆» `a "⋆") "*" `a)])])
       [])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       `tendsto_nhds_unique
       [`h₂
        (Term.app
         `pow_nnnorm_pow_one_div_tendsto_nhds_spectral_radius
         [(«term_*_» (Analysis.NormedSpace.Star.Spectrum.«term_⋆» `a "⋆") "*" `a)])])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       `pow_nnnorm_pow_one_div_tendsto_nhds_spectral_radius
       [(«term_*_» (Analysis.NormedSpace.Star.Spectrum.«term_⋆» `a "⋆") "*" `a)])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_*_»', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_*_»', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_*_» (Analysis.NormedSpace.Star.Spectrum.«term_⋆» `a "⋆") "*" `a)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `a
[PrettyPrinter.parenthesize] ...precedences are 71 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 70, term))
      (Analysis.NormedSpace.Star.Spectrum.«term_⋆» `a "⋆")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Analysis.NormedSpace.Star.Spectrum.«term_⋆»', expected 'Analysis.NormedSpace.Star.Spectrum.term_⋆._@.Analysis.NormedSpace.Star.Spectrum._hyg.7'
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
  IsStarNormal.spectral_radius_eq_nnnorm
  ( a : A ) [ IsStarNormal a ] : spectralRadius ℂ a = ‖ a ‖₊
  :=
    by
      refine' Ennreal.pow_strict_mono two_ne_zero . Injective _
        have
          heq
            :
              fun n : ℕ => ( ‖ a ⋆ * a ^ n ‖₊ ^ ( 1 / n : ℝ ) : ℝ≥0∞ )
                =
                fun x => x ^ 2 ∘ fun n : ℕ => ( ‖ a ^ n ‖₊ ^ ( 1 / n : ℝ ) : ℝ≥0∞ )
            :=
            by
              funext
                rw
                  [
                    Function.comp_apply
                      ,
                      ← rpow_nat_cast
                      ,
                      ← rpow_mul
                      ,
                      mul_comm
                      ,
                      rpow_mul
                      ,
                      rpow_nat_cast
                      ,
                      ← coe_pow
                      ,
                      sq
                      ,
                      ← nnnorm_star_mul_self
                      ,
                      Commute.mul_pow star_comm_self' a
                      ,
                      star_pow
                    ]
        have
          h₂
            :=
            Ennreal.continuous_pow 2 . Tendsto spectralRadius ℂ a . comp
              spectrum.pow_nnnorm_pow_one_div_tendsto_nhds_spectral_radius a
        rw [ ← HEq ] at h₂
        convert tendsto_nhds_unique h₂ pow_nnnorm_pow_one_div_tendsto_nhds_spectral_radius a ⋆ * a
        rw
          [
            IsSelfAdjoint.star_mul_self a . spectral_radius_eq_nnnorm
              ,
              sq
              ,
              nnnorm_star_mul_self
              ,
              coe_mul
            ]
#align is_star_normal.spectral_radius_eq_nnnorm IsStarNormal.spectral_radius_eq_nnnorm

/-- Any element of the spectrum of a selfadjoint is real. -/
theorem IsSelfAdjoint.mem_spectrum_eq_re [StarModule ℂ A] {a : A} (ha : IsSelfAdjoint a) {z : ℂ}
    (hz : z ∈ spectrum ℂ a) : z = z.re :=
  by
  let Iu := Units.mk0 I I_ne_zero
  have : exp ℂ (I • z) ∈ spectrum ℂ (exp ℂ (I • a)) := by
    simpa only [Units.smul_def, Units.val_mk0] using
      spectrum.exp_mem_exp (Iu • a) (smul_mem_smul_iff.mpr hz)
  exact
    Complex.ext (of_real_re _)
      (by
        simpa only [← Complex.exp_eq_exp_ℂ, mem_sphere_zero_iff_norm, norm_eq_abs, abs_exp,
          Real.exp_eq_one_iff, smul_eq_mul, I_mul, neg_eq_zero] using
          spectrum.subset_circle_of_unitary ha.exp_i_smul_unitary this)
#align is_self_adjoint.mem_spectrum_eq_re IsSelfAdjoint.mem_spectrum_eq_re

/-- Any element of the spectrum of a selfadjoint is real. -/
theorem selfAdjoint.mem_spectrum_eq_re [StarModule ℂ A] (a : selfAdjoint A) {z : ℂ}
    (hz : z ∈ spectrum ℂ (a : A)) : z = z.re :=
  a.Prop.mem_spectrum_eq_re hz
#align self_adjoint.mem_spectrum_eq_re selfAdjoint.mem_spectrum_eq_re

/-- The spectrum of a selfadjoint is real -/
theorem IsSelfAdjoint.coe_re_map_spectrum [StarModule ℂ A] {a : A} (ha : IsSelfAdjoint a) :
    spectrum ℂ a = (coe ∘ re '' spectrum ℂ a : Set ℂ) :=
  le_antisymm (fun z hz => ⟨z, hz, (ha.mem_spectrum_eq_re hz).symm⟩) fun z =>
    by
    rintro ⟨z, hz, rfl⟩
    simpa only [(ha.mem_spectrum_eq_re hz).symm, Function.comp_apply] using hz
#align is_self_adjoint.coe_re_map_spectrum IsSelfAdjoint.coe_re_map_spectrum

/-- The spectrum of a selfadjoint is real -/
theorem selfAdjoint.coe_re_map_spectrum [StarModule ℂ A] (a : selfAdjoint A) :
    spectrum ℂ (a : A) = (coe ∘ re '' spectrum ℂ (a : A) : Set ℂ) :=
  a.property.coe_re_map_spectrum
#align self_adjoint.coe_re_map_spectrum selfAdjoint.coe_re_map_spectrum

end ComplexScalars

namespace StarAlgHom

variable {F A B : Type _} [NormedRing A] [NormedAlgebra ℂ A] [CompleteSpace A] [StarRing A]
  [CstarRing A] [NormedRing B] [NormedAlgebra ℂ B] [CompleteSpace B] [StarRing B] [CstarRing B]
  [hF : StarAlgHomClass F ℂ A B] (φ : F)

include hF

/-- A star algebra homomorphism of complex C⋆-algebras is norm contractive. -/
theorem nnnorm_apply_le (a : A) : ‖(φ a : B)‖₊ ≤ ‖a‖₊ :=
  by
  suffices ∀ s : A, IsSelfAdjoint s → ‖φ s‖₊ ≤ ‖s‖₊ by
    exact
      nonneg_le_nonneg_of_sq_le_sq zero_le'
        (by
          simpa only [nnnorm_star_mul_self, map_star, map_mul] using
            this _ (IsSelfAdjoint.star_mul_self a))
  · intro s hs
    simpa only [hs.spectral_radius_eq_nnnorm, (hs.star_hom_apply φ).spectral_radius_eq_nnnorm,
      coe_le_coe] using
      show spectralRadius ℂ (φ s) ≤ spectralRadius ℂ s from
        supᵢ_le_supᵢ_of_subset (AlgHom.spectrum_apply_subset φ s)
#align star_alg_hom.nnnorm_apply_le StarAlgHom.nnnorm_apply_le

/-- A star algebra homomorphism of complex C⋆-algebras is norm contractive. -/
theorem norm_apply_le (a : A) : ‖(φ a : B)‖ ≤ ‖a‖ :=
  nnnorm_apply_le φ a
#align star_alg_hom.norm_apply_le StarAlgHom.norm_apply_le

/-- Star algebra homomorphisms between C⋆-algebras are continuous linear maps.
See note [lower instance priority] -/
noncomputable instance (priority := 100) : ContinuousLinearMapClass F ℂ A B :=
  { AlgHomClass.linearMapClass with
    map_continuous := fun φ =>
      AddMonoidHomClass.continuous_of_bound φ 1 (by simpa only [one_mul] using nnnorm_apply_le φ) }

end StarAlgHom

end

namespace WeakDual

open ContinuousMap Complex

open ComplexStarModule

variable {F A : Type _} [NormedRing A] [NormedAlgebra ℂ A] [CompleteSpace A] [StarRing A]
  [CstarRing A] [StarModule ℂ A] [hF : AlgHomClass F ℂ A ℂ]

include hF

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers
      [(Command.docComment
        "/--"
        "This instance is provided instead of `star_alg_hom_class` to avoid type class inference loops.\nSee note [lower instance priority] -/")]
      []
      []
      [(Command.noncomputable "noncomputable")]
      []
      [])
     (Command.instance
      (Term.attrKind [])
      "instance"
      [(Command.namedPrio "(" "priority" ":=" (num "100") ")")]
      []
      (Command.declSig
       []
       (Term.typeSpec ":" (Term.app `StarHomClass [`F `A (Data.Complex.Basic.termℂ "ℂ")])))
      (Command.whereStructInst
       "where"
       [(Command.whereStructField (Term.letDecl (Term.letIdDecl `coe [`φ] [] ":=" `φ)))
        []
        (Command.whereStructField
         (Term.letDecl (Term.letIdDecl `coe_injective' [] [] ":=" `FunLike.coe_injective')))
        []
        (Command.whereStructField
         (Term.letDecl
          (Term.letIdDecl
           `map_star
           [`φ `a]
           []
           ":="
           (Term.byTactic
            "by"
            (Tactic.tacticSeq
             (Tactic.tacticSeq1Indented
              [(Mathlib.Tactic.tacticSuffices_
                "suffices"
                [`hsa []]
                [(Term.typeSpec
                  ":"
                  (Term.forall
                   "∀"
                   [`s]
                   [(Term.typeSpec ":" (Term.app `selfAdjoint [`A]))]
                   ","
                   («term_=_»
                    (Analysis.NormedSpace.Star.Spectrum.«term_⋆» (Term.app `φ [`s]) "⋆")
                    "="
                    (Term.app `φ [`s]))))])
               []
               (tactic__
                (cdotTk (patternIgnore (token.«· » "·")))
                [(Tactic.rwSeq
                  "rw"
                  []
                  (Tactic.rwRuleSeq
                   "["
                   [(Tactic.rwRule
                     [(patternIgnore (token.«← » "←"))]
                     (Term.app `real_part_add_I_smul_imaginary_part [`a]))]
                   "]")
                  [])
                 []
                 (Tactic.simp
                  "simp"
                  []
                  []
                  ["only"]
                  ["["
                   [(Tactic.simpLemma [] [] `map_add)
                    ","
                    (Tactic.simpLemma [] [] `map_smul)
                    ","
                    (Tactic.simpLemma [] [] `star_add)
                    ","
                    (Tactic.simpLemma [] [] `star_smul)
                    ","
                    (Tactic.simpLemma [] [] `hsa)
                    ","
                    (Tactic.simpLemma [] [] `selfAdjoint.star_coe_eq)]
                   "]"]
                  [])])
               []
               (tactic__
                (cdotTk (patternIgnore (token.«· » "·")))
                [(Tactic.intro "intro" [`s])
                 []
                 (Tactic.tacticHave_
                  "have"
                  (Term.haveDecl
                   (Term.haveIdDecl
                    []
                    []
                    ":="
                    (Term.app
                     `AlgHom.apply_mem_spectrum
                     [`φ (Term.typeAscription "(" `s ":" [`A] ")")]))))
                 []
                 (Tactic.rwSeq
                  "rw"
                  []
                  (Tactic.rwRuleSeq
                   "["
                   [(Tactic.rwRule [] (Term.app `selfAdjoint.coe_re_map_spectrum [`s]))]
                   "]")
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
                         (Std.Tactic.RCases.rcasesPatMed
                          [(Std.Tactic.RCases.rcasesPat.tuple
                            "⟨"
                            [(Std.Tactic.RCases.rcasesPatLo
                              (Std.Tactic.RCases.rcasesPatMed
                               [(Std.Tactic.RCases.rcasesPat.ignore "_")])
                              [])
                             ","
                             (Std.Tactic.RCases.rcasesPatLo
                              (Std.Tactic.RCases.rcasesPatMed
                               [(Std.Tactic.RCases.rcasesPat.ignore "_")])
                              [])]
                            "⟩")])
                         [])
                        ","
                        (Std.Tactic.RCases.rcasesPatLo
                         (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.ignore "_")])
                         [])
                        ","
                        (Std.Tactic.RCases.rcasesPatLo
                         (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `heq)])
                         [])]
                       "⟩")])
                    [])])
                 []
                 (Tactic.rwSeq
                  "rw"
                  []
                  (Tactic.rwRuleSeq
                   "["
                   [(Tactic.rwRule [(patternIgnore (token.«← » "←"))] `HEq)
                    ","
                    (Tactic.rwRule [] `IsROrC.star_def)
                    ","
                    (Tactic.rwRule [] `IsROrC.conj_of_real)]
                   "]")
                  [])])]))))))]
       [])
      []
      []))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.instance', expected 'Lean.Parser.Command.abbrev'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.instance', expected 'Lean.Parser.Command.def'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.instance', expected 'Lean.Parser.Command.theorem'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.instance', expected 'Lean.Parser.Command.opaque'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.whereStructInst', expected 'Lean.Parser.Command.declValSimple'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.whereStructInst', expected 'Lean.Parser.Command.declValEqns'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.byTactic
       "by"
       (Tactic.tacticSeq
        (Tactic.tacticSeq1Indented
         [(Mathlib.Tactic.tacticSuffices_
           "suffices"
           [`hsa []]
           [(Term.typeSpec
             ":"
             (Term.forall
              "∀"
              [`s]
              [(Term.typeSpec ":" (Term.app `selfAdjoint [`A]))]
              ","
              («term_=_»
               (Analysis.NormedSpace.Star.Spectrum.«term_⋆» (Term.app `φ [`s]) "⋆")
               "="
               (Term.app `φ [`s]))))])
          []
          (tactic__
           (cdotTk (patternIgnore (token.«· » "·")))
           [(Tactic.rwSeq
             "rw"
             []
             (Tactic.rwRuleSeq
              "["
              [(Tactic.rwRule
                [(patternIgnore (token.«← » "←"))]
                (Term.app `real_part_add_I_smul_imaginary_part [`a]))]
              "]")
             [])
            []
            (Tactic.simp
             "simp"
             []
             []
             ["only"]
             ["["
              [(Tactic.simpLemma [] [] `map_add)
               ","
               (Tactic.simpLemma [] [] `map_smul)
               ","
               (Tactic.simpLemma [] [] `star_add)
               ","
               (Tactic.simpLemma [] [] `star_smul)
               ","
               (Tactic.simpLemma [] [] `hsa)
               ","
               (Tactic.simpLemma [] [] `selfAdjoint.star_coe_eq)]
              "]"]
             [])])
          []
          (tactic__
           (cdotTk (patternIgnore (token.«· » "·")))
           [(Tactic.intro "intro" [`s])
            []
            (Tactic.tacticHave_
             "have"
             (Term.haveDecl
              (Term.haveIdDecl
               []
               []
               ":="
               (Term.app
                `AlgHom.apply_mem_spectrum
                [`φ (Term.typeAscription "(" `s ":" [`A] ")")]))))
            []
            (Tactic.rwSeq
             "rw"
             []
             (Tactic.rwRuleSeq
              "["
              [(Tactic.rwRule [] (Term.app `selfAdjoint.coe_re_map_spectrum [`s]))]
              "]")
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
                    (Std.Tactic.RCases.rcasesPatMed
                     [(Std.Tactic.RCases.rcasesPat.tuple
                       "⟨"
                       [(Std.Tactic.RCases.rcasesPatLo
                         (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.ignore "_")])
                         [])
                        ","
                        (Std.Tactic.RCases.rcasesPatLo
                         (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.ignore "_")])
                         [])]
                       "⟩")])
                    [])
                   ","
                   (Std.Tactic.RCases.rcasesPatLo
                    (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.ignore "_")])
                    [])
                   ","
                   (Std.Tactic.RCases.rcasesPatLo
                    (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `heq)])
                    [])]
                  "⟩")])
               [])])
            []
            (Tactic.rwSeq
             "rw"
             []
             (Tactic.rwRuleSeq
              "["
              [(Tactic.rwRule [(patternIgnore (token.«← » "←"))] `HEq)
               ","
               (Tactic.rwRule [] `IsROrC.star_def)
               ","
               (Tactic.rwRule [] `IsROrC.conj_of_real)]
              "]")
             [])])])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (tactic__
       (cdotTk (patternIgnore (token.«· » "·")))
       [(Tactic.intro "intro" [`s])
        []
        (Tactic.tacticHave_
         "have"
         (Term.haveDecl
          (Term.haveIdDecl
           []
           []
           ":="
           (Term.app `AlgHom.apply_mem_spectrum [`φ (Term.typeAscription "(" `s ":" [`A] ")")]))))
        []
        (Tactic.rwSeq
         "rw"
         []
         (Tactic.rwRuleSeq
          "["
          [(Tactic.rwRule [] (Term.app `selfAdjoint.coe_re_map_spectrum [`s]))]
          "]")
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
                (Std.Tactic.RCases.rcasesPatMed
                 [(Std.Tactic.RCases.rcasesPat.tuple
                   "⟨"
                   [(Std.Tactic.RCases.rcasesPatLo
                     (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.ignore "_")])
                     [])
                    ","
                    (Std.Tactic.RCases.rcasesPatLo
                     (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.ignore "_")])
                     [])]
                   "⟩")])
                [])
               ","
               (Std.Tactic.RCases.rcasesPatLo
                (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.ignore "_")])
                [])
               ","
               (Std.Tactic.RCases.rcasesPatLo
                (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `heq)])
                [])]
              "⟩")])
           [])])
        []
        (Tactic.rwSeq
         "rw"
         []
         (Tactic.rwRuleSeq
          "["
          [(Tactic.rwRule [(patternIgnore (token.«← » "←"))] `HEq)
           ","
           (Tactic.rwRule [] `IsROrC.star_def)
           ","
           (Tactic.rwRule [] `IsROrC.conj_of_real)]
          "]")
         [])])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.rwSeq
       "rw"
       []
       (Tactic.rwRuleSeq
        "["
        [(Tactic.rwRule [(patternIgnore (token.«← » "←"))] `HEq)
         ","
         (Tactic.rwRule [] `IsROrC.star_def)
         ","
         (Tactic.rwRule [] `IsROrC.conj_of_real)]
        "]")
       [])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `IsROrC.conj_of_real
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `IsROrC.star_def
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `HEq
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
              (Std.Tactic.RCases.rcasesPatMed
               [(Std.Tactic.RCases.rcasesPat.tuple
                 "⟨"
                 [(Std.Tactic.RCases.rcasesPatLo
                   (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.ignore "_")])
                   [])
                  ","
                  (Std.Tactic.RCases.rcasesPatLo
                   (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.ignore "_")])
                   [])]
                 "⟩")])
              [])
             ","
             (Std.Tactic.RCases.rcasesPatLo
              (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.ignore "_")])
              [])
             ","
             (Std.Tactic.RCases.rcasesPatLo
              (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `heq)])
              [])]
            "⟩")])
         [])])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `this
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.rwSeq
       "rw"
       []
       (Tactic.rwRuleSeq
        "["
        [(Tactic.rwRule [] (Term.app `selfAdjoint.coe_re_map_spectrum [`s]))]
        "]")
       [(Tactic.location "at" (Tactic.locationHyp [`this] []))])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.locationHyp', expected 'Lean.Parser.Tactic.locationWildcard'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `this
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `selfAdjoint.coe_re_map_spectrum [`s])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `s
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `selfAdjoint.coe_re_map_spectrum
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
         (Term.app `AlgHom.apply_mem_spectrum [`φ (Term.typeAscription "(" `s ":" [`A] ")")]))))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `AlgHom.apply_mem_spectrum [`φ (Term.typeAscription "(" `s ":" [`A] ")")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.typeAscription', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.typeAscription', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.typeAscription "(" `s ":" [`A] ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `A
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `s
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, term))
      `φ
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1023, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `AlgHom.apply_mem_spectrum
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.intro "intro" [`s])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `s
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (tactic__
       (cdotTk (patternIgnore (token.«· » "·")))
       [(Tactic.rwSeq
         "rw"
         []
         (Tactic.rwRuleSeq
          "["
          [(Tactic.rwRule
            [(patternIgnore (token.«← » "←"))]
            (Term.app `real_part_add_I_smul_imaginary_part [`a]))]
          "]")
         [])
        []
        (Tactic.simp
         "simp"
         []
         []
         ["only"]
         ["["
          [(Tactic.simpLemma [] [] `map_add)
           ","
           (Tactic.simpLemma [] [] `map_smul)
           ","
           (Tactic.simpLemma [] [] `star_add)
           ","
           (Tactic.simpLemma [] [] `star_smul)
           ","
           (Tactic.simpLemma [] [] `hsa)
           ","
           (Tactic.simpLemma [] [] `selfAdjoint.star_coe_eq)]
          "]"]
         [])])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.simp
       "simp"
       []
       []
       ["only"]
       ["["
        [(Tactic.simpLemma [] [] `map_add)
         ","
         (Tactic.simpLemma [] [] `map_smul)
         ","
         (Tactic.simpLemma [] [] `star_add)
         ","
         (Tactic.simpLemma [] [] `star_smul)
         ","
         (Tactic.simpLemma [] [] `hsa)
         ","
         (Tactic.simpLemma [] [] `selfAdjoint.star_coe_eq)]
        "]"]
       [])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `selfAdjoint.star_coe_eq
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `hsa
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `star_smul
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `star_add
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `map_smul
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `map_add
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
          [(patternIgnore (token.«← » "←"))]
          (Term.app `real_part_add_I_smul_imaginary_part [`a]))]
        "]")
       [])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `real_part_add_I_smul_imaginary_part [`a])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `a
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `real_part_add_I_smul_imaginary_part
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Mathlib.Tactic.tacticSuffices_
       "suffices"
       [`hsa []]
       [(Term.typeSpec
         ":"
         (Term.forall
          "∀"
          [`s]
          [(Term.typeSpec ":" (Term.app `selfAdjoint [`A]))]
          ","
          («term_=_»
           (Analysis.NormedSpace.Star.Spectrum.«term_⋆» (Term.app `φ [`s]) "⋆")
           "="
           (Term.app `φ [`s]))))])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.forall
       "∀"
       [`s]
       [(Term.typeSpec ":" (Term.app `selfAdjoint [`A]))]
       ","
       («term_=_»
        (Analysis.NormedSpace.Star.Spectrum.«term_⋆» (Term.app `φ [`s]) "⋆")
        "="
        (Term.app `φ [`s])))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_=_»
       (Analysis.NormedSpace.Star.Spectrum.«term_⋆» (Term.app `φ [`s]) "⋆")
       "="
       (Term.app `φ [`s]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `φ [`s])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `s
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `φ
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 50, term))
      (Analysis.NormedSpace.Star.Spectrum.«term_⋆» (Term.app `φ [`s]) "⋆")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Analysis.NormedSpace.Star.Spectrum.«term_⋆»', expected 'Analysis.NormedSpace.Star.Spectrum.term_⋆._@.Analysis.NormedSpace.Star.Spectrum._hyg.7'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.letIdDecl', expected 'Lean.Parser.Term.letPatDecl'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.letIdDecl', expected 'Lean.Parser.Term.letEqnsDecl'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.instance', expected 'Lean.Parser.Command.axiom'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.instance', expected 'Lean.Parser.Command.example'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.instance', expected 'Lean.Parser.Command.inductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.instance', expected 'Lean.Parser.Command.classInductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.instance', expected 'Lean.Parser.Command.structure'-/-- failed to format: format: uncaught backtrack exception
/--
      This instance is provided instead of `star_alg_hom_class` to avoid type class inference loops.
      See note [lower instance priority] -/
    noncomputable
  instance
    ( priority := 100 )
    : StarHomClass F A ℂ
    where
      coe φ := φ
        coe_injective' := FunLike.coe_injective'
        map_star
          φ a
          :=
          by
            suffices hsa : ∀ s : selfAdjoint A , φ s ⋆ = φ s
              ·
                rw [ ← real_part_add_I_smul_imaginary_part a ]
                  simp
                    only
                    [ map_add , map_smul , star_add , star_smul , hsa , selfAdjoint.star_coe_eq ]
              ·
                intro s
                  have := AlgHom.apply_mem_spectrum φ ( s : A )
                  rw [ selfAdjoint.coe_re_map_spectrum s ] at this
                  rcases this with ⟨ ⟨ _ , _ ⟩ , _ , heq ⟩
                  rw [ ← HEq , IsROrC.star_def , IsROrC.conj_of_real ]

/-- This is not an instance to avoid type class inference loops. See
`weak_dual.complex.star_hom_class`. -/
noncomputable def AlgHomClass.starAlgHomClass : StarAlgHomClass F ℂ A ℂ :=
  { WeakDual.Complex.starHomClass, hF with coe := fun f => f }
#align alg_hom_class.star_alg_hom_class AlgHomClass.starAlgHomClass

omit hF

namespace CharacterSpace

noncomputable instance : StarAlgHomClass (characterSpace ℂ A) ℂ A ℂ :=
  { AlgHomClass.starAlgHomClass with coe := fun f => f }

end CharacterSpace

end WeakDual

