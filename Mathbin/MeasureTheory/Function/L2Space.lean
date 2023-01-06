/-
Copyright (c) 2021 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne

! This file was ported from Lean 3 source module measure_theory.function.l2_space
! leanprover-community/mathlib commit 26f081a2fb920140ed5bc5cc5344e84bcc7cb2b2
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Analysis.InnerProductSpace.Basic
import Mathbin.MeasureTheory.Integral.SetIntegral

/-! # `L^2` space

If `E` is an inner product space over `𝕜` (`ℝ` or `ℂ`), then `Lp E 2 μ` (defined in `lp_space.lean`)
is also an inner product space, with inner product defined as `inner f g = ∫ a, ⟪f a, g a⟫ ∂μ`.

### Main results

* `mem_L1_inner` : for `f` and `g` in `Lp E 2 μ`, the pointwise inner product `λ x, ⟪f x, g x⟫`
  belongs to `Lp 𝕜 1 μ`.
* `integrable_inner` : for `f` and `g` in `Lp E 2 μ`, the pointwise inner product `λ x, ⟪f x, g x⟫`
  is integrable.
* `L2.inner_product_space` : `Lp E 2 μ` is an inner product space.

-/


noncomputable section

open TopologicalSpace MeasureTheory MeasureTheory.lp

open Nnreal Ennreal MeasureTheory

namespace MeasureTheory

section

variable {α F : Type _} {m : MeasurableSpace α} {μ : Measure α} [NormedAddCommGroup F]

theorem Memℒp.integrableSq {f : α → ℝ} (h : Memℒp f 2 μ) : Integrable (fun x => f x ^ 2) μ := by
  simpa [← mem_ℒp_one_iff_integrable] using h.norm_rpow Ennreal.two_ne_zero Ennreal.two_ne_top
#align measure_theory.mem_ℒp.integrable_sq MeasureTheory.Memℒp.integrableSq

theorem mem_ℒp_two_iff_integrable_sq_norm {f : α → F} (hf : AeStronglyMeasurable f μ) :
    Memℒp f 2 μ ↔ Integrable (fun x => ‖f x‖ ^ 2) μ :=
  by
  rw [← mem_ℒp_one_iff_integrable]
  convert (mem_ℒp_norm_rpow_iff hf Ennreal.two_ne_zero Ennreal.two_ne_top).symm
  · simp
  · rw [div_eq_mul_inv, Ennreal.mul_inv_cancel Ennreal.two_ne_zero Ennreal.two_ne_top]
#align
  measure_theory.mem_ℒp_two_iff_integrable_sq_norm MeasureTheory.mem_ℒp_two_iff_integrable_sq_norm

theorem mem_ℒp_two_iff_integrable_sq {f : α → ℝ} (hf : AeStronglyMeasurable f μ) :
    Memℒp f 2 μ ↔ Integrable (fun x => f x ^ 2) μ :=
  by
  convert mem_ℒp_two_iff_integrable_sq_norm hf
  ext x
  simp
#align measure_theory.mem_ℒp_two_iff_integrable_sq MeasureTheory.mem_ℒp_two_iff_integrable_sq

end

namespace L2Cat

variable {α E F 𝕜 : Type _} [IsROrC 𝕜] [MeasurableSpace α] {μ : Measure α} [InnerProductSpace 𝕜 E]
  [NormedAddCommGroup F]

-- mathport name: «expr⟪ , ⟫»
local notation "⟪" x ", " y "⟫" => @inner 𝕜 _ _ x y

theorem snorm_rpow_two_norm_lt_top (f : lp F 2 μ) : snorm (fun x => ‖f x‖ ^ (2 : ℝ)) 1 μ < ∞ :=
  by
  have h_two : Ennreal.ofReal (2 : ℝ) = 2 := by simp [zero_le_one]
  rw [snorm_norm_rpow f zero_lt_two, one_mul, h_two]
  exact Ennreal.rpow_lt_top_of_nonneg zero_le_two (Lp.snorm_ne_top f)
#align measure_theory.L2.snorm_rpow_two_norm_lt_top MeasureTheory.L2Cat.snorm_rpow_two_norm_lt_top

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers [] [] [] [] [] [])
     (Command.theorem
      "theorem"
      (Command.declId `snorm_inner_lt_top [])
      (Command.declSig
       [(Term.explicitBinder
         "("
         [`f `g]
         [":" (MeasureTheory.MeasureTheory.Function.LpSpace.measure_theory.L2 `α " →₂[" `μ "] " `E)]
         []
         ")")]
       (Term.typeSpec
        ":"
        («term_<_»
         (Term.app
          `snorm
          [(Term.fun
            "fun"
            (Term.basicFun
             [`x]
             [(Term.typeSpec ":" `α)]
             "=>"
             (MeasureTheory.L2Cat.MeasureTheory.Function.L2Space.«term⟪_,_⟫»
              "⟪"
              (Term.app `f [`x])
              ", "
              (Term.app `g [`x])
              "⟫")))
           (num "1")
           `μ])
         "<"
         (Ennreal.Data.Real.Ennreal.ennreal.top "∞"))))
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
              [`h []]
              [(Term.typeSpec
                ":"
                (Term.forall
                 "∀"
                 [`x]
                 []
                 ","
                 («term_≤_»
                  (Term.app
                   `IsROrC.abs
                   [(MeasureTheory.L2Cat.MeasureTheory.Function.L2Space.«term⟪_,_⟫»
                     "⟪"
                     (Term.app `f [`x])
                     ", "
                     (Term.app `g [`x])
                     "⟫")])
                  "≤"
                  («term_*_»
                   (Analysis.Normed.Group.Basic.«term‖_‖» "‖" (Term.app `f [`x]) "‖")
                   "*"
                   (Analysis.Normed.Group.Basic.«term‖_‖» "‖" (Term.app `g [`x]) "‖")))))]
              ":="
              (Term.fun
               "fun"
               (Term.basicFun
                [`x]
                []
                "=>"
                (Term.app `abs_inner_le_norm [(Term.hole "_") (Term.hole "_")]))))))
           []
           (Tactic.tacticHave_
            "have"
            (Term.haveDecl
             (Term.haveIdDecl
              [`h' []]
              [(Term.typeSpec
                ":"
                (Term.forall
                 "∀"
                 [`x]
                 []
                 ","
                 («term_≤_»
                  (Term.app
                   `IsROrC.abs
                   [(MeasureTheory.L2Cat.MeasureTheory.Function.L2Space.«term⟪_,_⟫»
                     "⟪"
                     (Term.app `f [`x])
                     ", "
                     (Term.app `g [`x])
                     "⟫")])
                  "≤"
                  (Term.app
                   `IsROrC.abs
                   [(«term_+_»
                     («term_^_»
                      (Analysis.Normed.Group.Basic.«term‖_‖» "‖" (Term.app `f [`x]) "‖")
                      "^"
                      (num "2"))
                     "+"
                     («term_^_»
                      (Analysis.Normed.Group.Basic.«term‖_‖» "‖" (Term.app `g [`x]) "‖")
                      "^"
                      (num "2")))]))))]
              ":="
              (Term.byTactic
               "by"
               (Tactic.tacticSeq
                (Tactic.tacticSeq1Indented
                 [(Tactic.refine'
                   "refine'"
                   (Term.fun
                    "fun"
                    (Term.basicFun
                     [`x]
                     []
                     "=>"
                     (Term.app `le_trans [(Term.app `h [`x]) (Term.hole "_")]))))
                  []
                  (Tactic.rwSeq
                   "rw"
                   []
                   (Tactic.rwRuleSeq
                    "["
                    [(Tactic.rwRule [] `IsROrC.abs_to_real) "," (Tactic.rwRule [] `abs_eq_self.mpr)]
                    "]")
                   [])
                  []
                  (Mathlib.Tactic.tacticSwap "swap")
                  []
                  (tactic__
                   (cdotTk (patternIgnore (token.«· » "·")))
                   [(Tactic.exact
                     "exact"
                     (Term.app
                      `add_nonneg
                      [(Term.byTactic
                        "by"
                        (Tactic.tacticSeq
                         (Tactic.tacticSeq1Indented [(Tactic.simp "simp" [] [] [] [] [])])))
                       (Term.byTactic
                        "by"
                        (Tactic.tacticSeq
                         (Tactic.tacticSeq1Indented [(Tactic.simp "simp" [] [] [] [] [])])))]))])
                  []
                  (Tactic.refine'
                   "refine'"
                   (Term.app
                    `le_trans
                    [(Term.hole "_")
                     (Term.app
                      `half_le_self
                      [(Term.app
                        `add_nonneg
                        [(Term.app `sq_nonneg [(Term.hole "_")])
                         (Term.app `sq_nonneg [(Term.hole "_")])])])]))
                  []
                  (Tactic.refine'
                   "refine'"
                   (Term.app
                    (Term.proj
                     (Term.app `le_div_iff [(Term.app `zero_lt_two' [(Data.Real.Basic.termℝ "ℝ")])])
                     "."
                     `mpr)
                    [(Term.app
                      (Term.proj (Term.app `le_of_eq [(Term.hole "_")]) "." `trans)
                      [(Term.app `two_mul_le_add_sq [(Term.hole "_") (Term.hole "_")])])]))
                  []
                  (Mathlib.Tactic.RingNF.ring "ring")]))))))
           []
           (Mathlib.Tactic.tacticSimp_rw__
            "simp_rw"
            (Tactic.rwRuleSeq
             "["
             [(Tactic.rwRule [(patternIgnore (token.«← » "←"))] `IsROrC.norm_eq_abs)
              ","
              (Tactic.rwRule [(patternIgnore (token.«← » "←"))] `Real.rpow_nat_cast)]
             "]")
            [(Tactic.location "at" (Tactic.locationHyp [`h'] []))])
           []
           (Tactic.refine'
            "refine'"
            (Term.app
             (Term.proj
              (Term.app `snorm_mono_ae [(Term.app `ae_of_all [(Term.hole "_") `h'])])
              "."
              `trans_lt)
             [(Term.app
               (Term.proj
                (Term.app `snorm_add_le [(Term.hole "_") (Term.hole "_") `le_rfl])
                "."
                `trans_lt)
               [(Term.hole "_")])]))
           []
           (tactic__
            (cdotTk (patternIgnore (token.«· » "·")))
            [(Tactic.exact
              "exact"
              (Term.proj
               (Term.app
                (Term.proj
                 (Term.proj
                  (Term.proj (Term.app `Lp.ae_strongly_measurable [`f]) "." `norm)
                  "."
                  `AeMeasurable)
                 "."
                 `pow_const)
                [(Term.hole "_")])
               "."
               `AeStronglyMeasurable))])
           []
           (tactic__
            (cdotTk (patternIgnore (token.«· » "·")))
            [(Tactic.exact
              "exact"
              (Term.proj
               (Term.app
                (Term.proj
                 (Term.proj
                  (Term.proj (Term.app `Lp.ae_strongly_measurable [`g]) "." `norm)
                  "."
                  `AeMeasurable)
                 "."
                 `pow_const)
                [(Term.hole "_")])
               "."
               `AeStronglyMeasurable))])
           []
           (Tactic.simp
            "simp"
            []
            []
            ["only"]
            ["["
             [(Tactic.simpLemma [] [] `Nat.cast_bit0)
              ","
              (Tactic.simpLemma [] [] `Ennreal.add_lt_top)
              ","
              (Tactic.simpLemma [] [] `Nat.cast_one)]
             "]"]
            [])
           []
           (Tactic.exact
            "exact"
            (Term.anonymousCtor
             "⟨"
             [(Term.app `snorm_rpow_two_norm_lt_top [`f])
              ","
              (Term.app `snorm_rpow_two_norm_lt_top [`g])]
             "⟩"))])))
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
             [`h []]
             [(Term.typeSpec
               ":"
               (Term.forall
                "∀"
                [`x]
                []
                ","
                («term_≤_»
                 (Term.app
                  `IsROrC.abs
                  [(MeasureTheory.L2Cat.MeasureTheory.Function.L2Space.«term⟪_,_⟫»
                    "⟪"
                    (Term.app `f [`x])
                    ", "
                    (Term.app `g [`x])
                    "⟫")])
                 "≤"
                 («term_*_»
                  (Analysis.Normed.Group.Basic.«term‖_‖» "‖" (Term.app `f [`x]) "‖")
                  "*"
                  (Analysis.Normed.Group.Basic.«term‖_‖» "‖" (Term.app `g [`x]) "‖")))))]
             ":="
             (Term.fun
              "fun"
              (Term.basicFun
               [`x]
               []
               "=>"
               (Term.app `abs_inner_le_norm [(Term.hole "_") (Term.hole "_")]))))))
          []
          (Tactic.tacticHave_
           "have"
           (Term.haveDecl
            (Term.haveIdDecl
             [`h' []]
             [(Term.typeSpec
               ":"
               (Term.forall
                "∀"
                [`x]
                []
                ","
                («term_≤_»
                 (Term.app
                  `IsROrC.abs
                  [(MeasureTheory.L2Cat.MeasureTheory.Function.L2Space.«term⟪_,_⟫»
                    "⟪"
                    (Term.app `f [`x])
                    ", "
                    (Term.app `g [`x])
                    "⟫")])
                 "≤"
                 (Term.app
                  `IsROrC.abs
                  [(«term_+_»
                    («term_^_»
                     (Analysis.Normed.Group.Basic.«term‖_‖» "‖" (Term.app `f [`x]) "‖")
                     "^"
                     (num "2"))
                    "+"
                    («term_^_»
                     (Analysis.Normed.Group.Basic.«term‖_‖» "‖" (Term.app `g [`x]) "‖")
                     "^"
                     (num "2")))]))))]
             ":="
             (Term.byTactic
              "by"
              (Tactic.tacticSeq
               (Tactic.tacticSeq1Indented
                [(Tactic.refine'
                  "refine'"
                  (Term.fun
                   "fun"
                   (Term.basicFun
                    [`x]
                    []
                    "=>"
                    (Term.app `le_trans [(Term.app `h [`x]) (Term.hole "_")]))))
                 []
                 (Tactic.rwSeq
                  "rw"
                  []
                  (Tactic.rwRuleSeq
                   "["
                   [(Tactic.rwRule [] `IsROrC.abs_to_real) "," (Tactic.rwRule [] `abs_eq_self.mpr)]
                   "]")
                  [])
                 []
                 (Mathlib.Tactic.tacticSwap "swap")
                 []
                 (tactic__
                  (cdotTk (patternIgnore (token.«· » "·")))
                  [(Tactic.exact
                    "exact"
                    (Term.app
                     `add_nonneg
                     [(Term.byTactic
                       "by"
                       (Tactic.tacticSeq
                        (Tactic.tacticSeq1Indented [(Tactic.simp "simp" [] [] [] [] [])])))
                      (Term.byTactic
                       "by"
                       (Tactic.tacticSeq
                        (Tactic.tacticSeq1Indented [(Tactic.simp "simp" [] [] [] [] [])])))]))])
                 []
                 (Tactic.refine'
                  "refine'"
                  (Term.app
                   `le_trans
                   [(Term.hole "_")
                    (Term.app
                     `half_le_self
                     [(Term.app
                       `add_nonneg
                       [(Term.app `sq_nonneg [(Term.hole "_")])
                        (Term.app `sq_nonneg [(Term.hole "_")])])])]))
                 []
                 (Tactic.refine'
                  "refine'"
                  (Term.app
                   (Term.proj
                    (Term.app `le_div_iff [(Term.app `zero_lt_two' [(Data.Real.Basic.termℝ "ℝ")])])
                    "."
                    `mpr)
                   [(Term.app
                     (Term.proj (Term.app `le_of_eq [(Term.hole "_")]) "." `trans)
                     [(Term.app `two_mul_le_add_sq [(Term.hole "_") (Term.hole "_")])])]))
                 []
                 (Mathlib.Tactic.RingNF.ring "ring")]))))))
          []
          (Mathlib.Tactic.tacticSimp_rw__
           "simp_rw"
           (Tactic.rwRuleSeq
            "["
            [(Tactic.rwRule [(patternIgnore (token.«← » "←"))] `IsROrC.norm_eq_abs)
             ","
             (Tactic.rwRule [(patternIgnore (token.«← » "←"))] `Real.rpow_nat_cast)]
            "]")
           [(Tactic.location "at" (Tactic.locationHyp [`h'] []))])
          []
          (Tactic.refine'
           "refine'"
           (Term.app
            (Term.proj
             (Term.app `snorm_mono_ae [(Term.app `ae_of_all [(Term.hole "_") `h'])])
             "."
             `trans_lt)
            [(Term.app
              (Term.proj
               (Term.app `snorm_add_le [(Term.hole "_") (Term.hole "_") `le_rfl])
               "."
               `trans_lt)
              [(Term.hole "_")])]))
          []
          (tactic__
           (cdotTk (patternIgnore (token.«· » "·")))
           [(Tactic.exact
             "exact"
             (Term.proj
              (Term.app
               (Term.proj
                (Term.proj
                 (Term.proj (Term.app `Lp.ae_strongly_measurable [`f]) "." `norm)
                 "."
                 `AeMeasurable)
                "."
                `pow_const)
               [(Term.hole "_")])
              "."
              `AeStronglyMeasurable))])
          []
          (tactic__
           (cdotTk (patternIgnore (token.«· » "·")))
           [(Tactic.exact
             "exact"
             (Term.proj
              (Term.app
               (Term.proj
                (Term.proj
                 (Term.proj (Term.app `Lp.ae_strongly_measurable [`g]) "." `norm)
                 "."
                 `AeMeasurable)
                "."
                `pow_const)
               [(Term.hole "_")])
              "."
              `AeStronglyMeasurable))])
          []
          (Tactic.simp
           "simp"
           []
           []
           ["only"]
           ["["
            [(Tactic.simpLemma [] [] `Nat.cast_bit0)
             ","
             (Tactic.simpLemma [] [] `Ennreal.add_lt_top)
             ","
             (Tactic.simpLemma [] [] `Nat.cast_one)]
            "]"]
           [])
          []
          (Tactic.exact
           "exact"
           (Term.anonymousCtor
            "⟨"
            [(Term.app `snorm_rpow_two_norm_lt_top [`f])
             ","
             (Term.app `snorm_rpow_two_norm_lt_top [`g])]
            "⟩"))])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.exact
       "exact"
       (Term.anonymousCtor
        "⟨"
        [(Term.app `snorm_rpow_two_norm_lt_top [`f])
         ","
         (Term.app `snorm_rpow_two_norm_lt_top [`g])]
        "⟩"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.anonymousCtor
       "⟨"
       [(Term.app `snorm_rpow_two_norm_lt_top [`f]) "," (Term.app `snorm_rpow_two_norm_lt_top [`g])]
       "⟩")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `snorm_rpow_two_norm_lt_top [`g])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `g
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `snorm_rpow_two_norm_lt_top
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `snorm_rpow_two_norm_lt_top [`f])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `f
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `snorm_rpow_two_norm_lt_top
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.simp
       "simp"
       []
       []
       ["only"]
       ["["
        [(Tactic.simpLemma [] [] `Nat.cast_bit0)
         ","
         (Tactic.simpLemma [] [] `Ennreal.add_lt_top)
         ","
         (Tactic.simpLemma [] [] `Nat.cast_one)]
        "]"]
       [])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `Nat.cast_one
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `Ennreal.add_lt_top
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `Nat.cast_bit0
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (tactic__
       (cdotTk (patternIgnore (token.«· » "·")))
       [(Tactic.exact
         "exact"
         (Term.proj
          (Term.app
           (Term.proj
            (Term.proj
             (Term.proj (Term.app `Lp.ae_strongly_measurable [`g]) "." `norm)
             "."
             `AeMeasurable)
            "."
            `pow_const)
           [(Term.hole "_")])
          "."
          `AeStronglyMeasurable))])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.exact
       "exact"
       (Term.proj
        (Term.app
         (Term.proj
          (Term.proj
           (Term.proj (Term.app `Lp.ae_strongly_measurable [`g]) "." `norm)
           "."
           `AeMeasurable)
          "."
          `pow_const)
         [(Term.hole "_")])
        "."
        `AeStronglyMeasurable))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.proj
       (Term.app
        (Term.proj
         (Term.proj
          (Term.proj (Term.app `Lp.ae_strongly_measurable [`g]) "." `norm)
          "."
          `AeMeasurable)
         "."
         `pow_const)
        [(Term.hole "_")])
       "."
       `AeStronglyMeasurable)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.app
       (Term.proj
        (Term.proj
         (Term.proj (Term.app `Lp.ae_strongly_measurable [`g]) "." `norm)
         "."
         `AeMeasurable)
        "."
        `pow_const)
       [(Term.hole "_")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (Term.proj
       (Term.proj
        (Term.proj (Term.app `Lp.ae_strongly_measurable [`g]) "." `norm)
        "."
        `AeMeasurable)
       "."
       `pow_const)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.proj (Term.proj (Term.app `Lp.ae_strongly_measurable [`g]) "." `norm) "." `AeMeasurable)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.proj (Term.app `Lp.ae_strongly_measurable [`g]) "." `norm)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.app `Lp.ae_strongly_measurable [`g])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `g
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `Lp.ae_strongly_measurable
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.app `Lp.ae_strongly_measurable [`g])
     ")")
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.app
      (Term.proj
       (Term.proj
        (Term.proj (Term.paren "(" (Term.app `Lp.ae_strongly_measurable [`g]) ")") "." `norm)
        "."
        `AeMeasurable)
       "."
       `pow_const)
      [(Term.hole "_")])
     ")")
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (tactic__
       (cdotTk (patternIgnore (token.«· » "·")))
       [(Tactic.exact
         "exact"
         (Term.proj
          (Term.app
           (Term.proj
            (Term.proj
             (Term.proj (Term.app `Lp.ae_strongly_measurable [`f]) "." `norm)
             "."
             `AeMeasurable)
            "."
            `pow_const)
           [(Term.hole "_")])
          "."
          `AeStronglyMeasurable))])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.exact
       "exact"
       (Term.proj
        (Term.app
         (Term.proj
          (Term.proj
           (Term.proj (Term.app `Lp.ae_strongly_measurable [`f]) "." `norm)
           "."
           `AeMeasurable)
          "."
          `pow_const)
         [(Term.hole "_")])
        "."
        `AeStronglyMeasurable))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.proj
       (Term.app
        (Term.proj
         (Term.proj
          (Term.proj (Term.app `Lp.ae_strongly_measurable [`f]) "." `norm)
          "."
          `AeMeasurable)
         "."
         `pow_const)
        [(Term.hole "_")])
       "."
       `AeStronglyMeasurable)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.app
       (Term.proj
        (Term.proj
         (Term.proj (Term.app `Lp.ae_strongly_measurable [`f]) "." `norm)
         "."
         `AeMeasurable)
        "."
        `pow_const)
       [(Term.hole "_")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (Term.proj
       (Term.proj
        (Term.proj (Term.app `Lp.ae_strongly_measurable [`f]) "." `norm)
        "."
        `AeMeasurable)
       "."
       `pow_const)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.proj (Term.proj (Term.app `Lp.ae_strongly_measurable [`f]) "." `norm) "." `AeMeasurable)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.proj (Term.app `Lp.ae_strongly_measurable [`f]) "." `norm)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.app `Lp.ae_strongly_measurable [`f])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `f
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `Lp.ae_strongly_measurable
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.app `Lp.ae_strongly_measurable [`f])
     ")")
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.app
      (Term.proj
       (Term.proj
        (Term.proj (Term.paren "(" (Term.app `Lp.ae_strongly_measurable [`f]) ")") "." `norm)
        "."
        `AeMeasurable)
       "."
       `pow_const)
      [(Term.hole "_")])
     ")")
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.refine'
       "refine'"
       (Term.app
        (Term.proj
         (Term.app `snorm_mono_ae [(Term.app `ae_of_all [(Term.hole "_") `h'])])
         "."
         `trans_lt)
        [(Term.app
          (Term.proj
           (Term.app `snorm_add_le [(Term.hole "_") (Term.hole "_") `le_rfl])
           "."
           `trans_lt)
          [(Term.hole "_")])]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       (Term.proj
        (Term.app `snorm_mono_ae [(Term.app `ae_of_all [(Term.hole "_") `h'])])
        "."
        `trans_lt)
       [(Term.app
         (Term.proj
          (Term.app `snorm_add_le [(Term.hole "_") (Term.hole "_") `le_rfl])
          "."
          `trans_lt)
         [(Term.hole "_")])])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       (Term.proj (Term.app `snorm_add_le [(Term.hole "_") (Term.hole "_") `le_rfl]) "." `trans_lt)
       [(Term.hole "_")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (Term.proj (Term.app `snorm_add_le [(Term.hole "_") (Term.hole "_") `le_rfl]) "." `trans_lt)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.app `snorm_add_le [(Term.hole "_") (Term.hole "_") `le_rfl])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `le_rfl
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
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
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `snorm_add_le
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.app `snorm_add_le [(Term.hole "_") (Term.hole "_") `le_rfl])
     ")")
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.app
      (Term.proj
       (Term.paren "(" (Term.app `snorm_add_le [(Term.hole "_") (Term.hole "_") `le_rfl]) ")")
       "."
       `trans_lt)
      [(Term.hole "_")])
     ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (Term.proj
       (Term.app `snorm_mono_ae [(Term.app `ae_of_all [(Term.hole "_") `h'])])
       "."
       `trans_lt)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.app `snorm_mono_ae [(Term.app `ae_of_all [(Term.hole "_") `h'])])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `ae_of_all [(Term.hole "_") `h'])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `h'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `ae_of_all
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.app `ae_of_all [(Term.hole "_") `h'])
     ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `snorm_mono_ae
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.app `snorm_mono_ae [(Term.paren "(" (Term.app `ae_of_all [(Term.hole "_") `h']) ")")])
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
        [(Tactic.rwRule [(patternIgnore (token.«← » "←"))] `IsROrC.norm_eq_abs)
         ","
         (Tactic.rwRule [(patternIgnore (token.«← » "←"))] `Real.rpow_nat_cast)]
        "]")
       [(Tactic.location "at" (Tactic.locationHyp [`h'] []))])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.locationHyp', expected 'Lean.Parser.Tactic.locationWildcard'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `h'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `Real.rpow_nat_cast
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `IsROrC.norm_eq_abs
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.tacticHave_
       "have"
       (Term.haveDecl
        (Term.haveIdDecl
         [`h' []]
         [(Term.typeSpec
           ":"
           (Term.forall
            "∀"
            [`x]
            []
            ","
            («term_≤_»
             (Term.app
              `IsROrC.abs
              [(MeasureTheory.L2Cat.MeasureTheory.Function.L2Space.«term⟪_,_⟫»
                "⟪"
                (Term.app `f [`x])
                ", "
                (Term.app `g [`x])
                "⟫")])
             "≤"
             (Term.app
              `IsROrC.abs
              [(«term_+_»
                («term_^_»
                 (Analysis.Normed.Group.Basic.«term‖_‖» "‖" (Term.app `f [`x]) "‖")
                 "^"
                 (num "2"))
                "+"
                («term_^_»
                 (Analysis.Normed.Group.Basic.«term‖_‖» "‖" (Term.app `g [`x]) "‖")
                 "^"
                 (num "2")))]))))]
         ":="
         (Term.byTactic
          "by"
          (Tactic.tacticSeq
           (Tactic.tacticSeq1Indented
            [(Tactic.refine'
              "refine'"
              (Term.fun
               "fun"
               (Term.basicFun
                [`x]
                []
                "=>"
                (Term.app `le_trans [(Term.app `h [`x]) (Term.hole "_")]))))
             []
             (Tactic.rwSeq
              "rw"
              []
              (Tactic.rwRuleSeq
               "["
               [(Tactic.rwRule [] `IsROrC.abs_to_real) "," (Tactic.rwRule [] `abs_eq_self.mpr)]
               "]")
              [])
             []
             (Mathlib.Tactic.tacticSwap "swap")
             []
             (tactic__
              (cdotTk (patternIgnore (token.«· » "·")))
              [(Tactic.exact
                "exact"
                (Term.app
                 `add_nonneg
                 [(Term.byTactic
                   "by"
                   (Tactic.tacticSeq
                    (Tactic.tacticSeq1Indented [(Tactic.simp "simp" [] [] [] [] [])])))
                  (Term.byTactic
                   "by"
                   (Tactic.tacticSeq
                    (Tactic.tacticSeq1Indented [(Tactic.simp "simp" [] [] [] [] [])])))]))])
             []
             (Tactic.refine'
              "refine'"
              (Term.app
               `le_trans
               [(Term.hole "_")
                (Term.app
                 `half_le_self
                 [(Term.app
                   `add_nonneg
                   [(Term.app `sq_nonneg [(Term.hole "_")])
                    (Term.app `sq_nonneg [(Term.hole "_")])])])]))
             []
             (Tactic.refine'
              "refine'"
              (Term.app
               (Term.proj
                (Term.app `le_div_iff [(Term.app `zero_lt_two' [(Data.Real.Basic.termℝ "ℝ")])])
                "."
                `mpr)
               [(Term.app
                 (Term.proj (Term.app `le_of_eq [(Term.hole "_")]) "." `trans)
                 [(Term.app `two_mul_le_add_sq [(Term.hole "_") (Term.hole "_")])])]))
             []
             (Mathlib.Tactic.RingNF.ring "ring")]))))))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.byTactic
       "by"
       (Tactic.tacticSeq
        (Tactic.tacticSeq1Indented
         [(Tactic.refine'
           "refine'"
           (Term.fun
            "fun"
            (Term.basicFun [`x] [] "=>" (Term.app `le_trans [(Term.app `h [`x]) (Term.hole "_")]))))
          []
          (Tactic.rwSeq
           "rw"
           []
           (Tactic.rwRuleSeq
            "["
            [(Tactic.rwRule [] `IsROrC.abs_to_real) "," (Tactic.rwRule [] `abs_eq_self.mpr)]
            "]")
           [])
          []
          (Mathlib.Tactic.tacticSwap "swap")
          []
          (tactic__
           (cdotTk (patternIgnore (token.«· » "·")))
           [(Tactic.exact
             "exact"
             (Term.app
              `add_nonneg
              [(Term.byTactic
                "by"
                (Tactic.tacticSeq
                 (Tactic.tacticSeq1Indented [(Tactic.simp "simp" [] [] [] [] [])])))
               (Term.byTactic
                "by"
                (Tactic.tacticSeq
                 (Tactic.tacticSeq1Indented [(Tactic.simp "simp" [] [] [] [] [])])))]))])
          []
          (Tactic.refine'
           "refine'"
           (Term.app
            `le_trans
            [(Term.hole "_")
             (Term.app
              `half_le_self
              [(Term.app
                `add_nonneg
                [(Term.app `sq_nonneg [(Term.hole "_")])
                 (Term.app `sq_nonneg [(Term.hole "_")])])])]))
          []
          (Tactic.refine'
           "refine'"
           (Term.app
            (Term.proj
             (Term.app `le_div_iff [(Term.app `zero_lt_two' [(Data.Real.Basic.termℝ "ℝ")])])
             "."
             `mpr)
            [(Term.app
              (Term.proj (Term.app `le_of_eq [(Term.hole "_")]) "." `trans)
              [(Term.app `two_mul_le_add_sq [(Term.hole "_") (Term.hole "_")])])]))
          []
          (Mathlib.Tactic.RingNF.ring "ring")])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Mathlib.Tactic.RingNF.ring "ring")
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.refine'
       "refine'"
       (Term.app
        (Term.proj
         (Term.app `le_div_iff [(Term.app `zero_lt_two' [(Data.Real.Basic.termℝ "ℝ")])])
         "."
         `mpr)
        [(Term.app
          (Term.proj (Term.app `le_of_eq [(Term.hole "_")]) "." `trans)
          [(Term.app `two_mul_le_add_sq [(Term.hole "_") (Term.hole "_")])])]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       (Term.proj
        (Term.app `le_div_iff [(Term.app `zero_lt_two' [(Data.Real.Basic.termℝ "ℝ")])])
        "."
        `mpr)
       [(Term.app
         (Term.proj (Term.app `le_of_eq [(Term.hole "_")]) "." `trans)
         [(Term.app `two_mul_le_add_sq [(Term.hole "_") (Term.hole "_")])])])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       (Term.proj (Term.app `le_of_eq [(Term.hole "_")]) "." `trans)
       [(Term.app `two_mul_le_add_sq [(Term.hole "_") (Term.hole "_")])])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `two_mul_le_add_sq [(Term.hole "_") (Term.hole "_")])
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
      `two_mul_le_add_sq
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.app `two_mul_le_add_sq [(Term.hole "_") (Term.hole "_")])
     ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (Term.proj (Term.app `le_of_eq [(Term.hole "_")]) "." `trans)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.app `le_of_eq [(Term.hole "_")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `le_of_eq
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.app `le_of_eq [(Term.hole "_")])
     ")")
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.app
      (Term.proj (Term.paren "(" (Term.app `le_of_eq [(Term.hole "_")]) ")") "." `trans)
      [(Term.paren "(" (Term.app `two_mul_le_add_sq [(Term.hole "_") (Term.hole "_")]) ")")])
     ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (Term.proj
       (Term.app `le_div_iff [(Term.app `zero_lt_two' [(Data.Real.Basic.termℝ "ℝ")])])
       "."
       `mpr)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.app `le_div_iff [(Term.app `zero_lt_two' [(Data.Real.Basic.termℝ "ℝ")])])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `zero_lt_two' [(Data.Real.Basic.termℝ "ℝ")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Data.Real.Basic.termℝ', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Data.Real.Basic.termℝ', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Data.Real.Basic.termℝ "ℝ")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `zero_lt_two'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.app `zero_lt_two' [(Data.Real.Basic.termℝ "ℝ")])
     ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `le_div_iff
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.app
      `le_div_iff
      [(Term.paren "(" (Term.app `zero_lt_two' [(Data.Real.Basic.termℝ "ℝ")]) ")")])
     ")")
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.refine'
       "refine'"
       (Term.app
        `le_trans
        [(Term.hole "_")
         (Term.app
          `half_le_self
          [(Term.app
            `add_nonneg
            [(Term.app `sq_nonneg [(Term.hole "_")]) (Term.app `sq_nonneg [(Term.hole "_")])])])]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       `le_trans
       [(Term.hole "_")
        (Term.app
         `half_le_self
         [(Term.app
           `add_nonneg
           [(Term.app `sq_nonneg [(Term.hole "_")]) (Term.app `sq_nonneg [(Term.hole "_")])])])])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       `half_le_self
       [(Term.app
         `add_nonneg
         [(Term.app `sq_nonneg [(Term.hole "_")]) (Term.app `sq_nonneg [(Term.hole "_")])])])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       `add_nonneg
       [(Term.app `sq_nonneg [(Term.hole "_")]) (Term.app `sq_nonneg [(Term.hole "_")])])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `sq_nonneg [(Term.hole "_")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `sq_nonneg
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.app `sq_nonneg [(Term.hole "_")])
     ")")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.app `sq_nonneg [(Term.hole "_")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.hole "_")
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
     (Term.app `sq_nonneg [(Term.hole "_")])
     ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `add_nonneg
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.app
      `add_nonneg
      [(Term.paren "(" (Term.app `sq_nonneg [(Term.hole "_")]) ")")
       (Term.paren "(" (Term.app `sq_nonneg [(Term.hole "_")]) ")")])
     ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `half_le_self
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.app
      `half_le_self
      [(Term.paren
        "("
        (Term.app
         `add_nonneg
         [(Term.paren "(" (Term.app `sq_nonneg [(Term.hole "_")]) ")")
          (Term.paren "(" (Term.app `sq_nonneg [(Term.hole "_")]) ")")])
        ")")])
     ")")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `le_trans
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (tactic__
       (cdotTk (patternIgnore (token.«· » "·")))
       [(Tactic.exact
         "exact"
         (Term.app
          `add_nonneg
          [(Term.byTactic
            "by"
            (Tactic.tacticSeq (Tactic.tacticSeq1Indented [(Tactic.simp "simp" [] [] [] [] [])])))
           (Term.byTactic
            "by"
            (Tactic.tacticSeq
             (Tactic.tacticSeq1Indented [(Tactic.simp "simp" [] [] [] [] [])])))]))])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.exact
       "exact"
       (Term.app
        `add_nonneg
        [(Term.byTactic
          "by"
          (Tactic.tacticSeq (Tactic.tacticSeq1Indented [(Tactic.simp "simp" [] [] [] [] [])])))
         (Term.byTactic
          "by"
          (Tactic.tacticSeq (Tactic.tacticSeq1Indented [(Tactic.simp "simp" [] [] [] [] [])])))]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       `add_nonneg
       [(Term.byTactic
         "by"
         (Tactic.tacticSeq (Tactic.tacticSeq1Indented [(Tactic.simp "simp" [] [] [] [] [])])))
        (Term.byTactic
         "by"
         (Tactic.tacticSeq (Tactic.tacticSeq1Indented [(Tactic.simp "simp" [] [] [] [] [])])))])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.byTactic', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.byTactic', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.byTactic
       "by"
       (Tactic.tacticSeq (Tactic.tacticSeq1Indented [(Tactic.simp "simp" [] [] [] [] [])])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.simp "simp" [] [] [] [] [])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 0,
     tactic) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.byTactic
      "by"
      (Tactic.tacticSeq (Tactic.tacticSeq1Indented [(Tactic.simp "simp" [] [] [] [] [])])))
     ")")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.byTactic', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.byTactic', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.byTactic
       "by"
       (Tactic.tacticSeq (Tactic.tacticSeq1Indented [(Tactic.simp "simp" [] [] [] [] [])])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.simp "simp" [] [] [] [] [])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 0, tactic) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.byTactic
      "by"
      (Tactic.tacticSeq (Tactic.tacticSeq1Indented [(Tactic.simp "simp" [] [] [] [] [])])))
     ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `add_nonneg
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Mathlib.Tactic.tacticSwap "swap")
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.rwSeq
       "rw"
       []
       (Tactic.rwRuleSeq
        "["
        [(Tactic.rwRule [] `IsROrC.abs_to_real) "," (Tactic.rwRule [] `abs_eq_self.mpr)]
        "]")
       [])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `abs_eq_self.mpr
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `IsROrC.abs_to_real
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.refine'
       "refine'"
       (Term.fun
        "fun"
        (Term.basicFun [`x] [] "=>" (Term.app `le_trans [(Term.app `h [`x]) (Term.hole "_")]))))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.fun
       "fun"
       (Term.basicFun [`x] [] "=>" (Term.app `le_trans [(Term.app `h [`x]) (Term.hole "_")])))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `le_trans [(Term.app `h [`x]) (Term.hole "_")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, term))
      (Term.app `h [`x])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `x
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `h
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023,
     term) <=? (some 1023, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren "(" (Term.app `h [`x]) ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `le_trans
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
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, tactic) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.forall
       "∀"
       [`x]
       []
       ","
       («term_≤_»
        (Term.app
         `IsROrC.abs
         [(MeasureTheory.L2Cat.MeasureTheory.Function.L2Space.«term⟪_,_⟫»
           "⟪"
           (Term.app `f [`x])
           ", "
           (Term.app `g [`x])
           "⟫")])
        "≤"
        (Term.app
         `IsROrC.abs
         [(«term_+_»
           («term_^_»
            (Analysis.Normed.Group.Basic.«term‖_‖» "‖" (Term.app `f [`x]) "‖")
            "^"
            (num "2"))
           "+"
           («term_^_»
            (Analysis.Normed.Group.Basic.«term‖_‖» "‖" (Term.app `g [`x]) "‖")
            "^"
            (num "2")))])))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_≤_»
       (Term.app
        `IsROrC.abs
        [(MeasureTheory.L2Cat.MeasureTheory.Function.L2Space.«term⟪_,_⟫»
          "⟪"
          (Term.app `f [`x])
          ", "
          (Term.app `g [`x])
          "⟫")])
       "≤"
       (Term.app
        `IsROrC.abs
        [(«term_+_»
          («term_^_»
           (Analysis.Normed.Group.Basic.«term‖_‖» "‖" (Term.app `f [`x]) "‖")
           "^"
           (num "2"))
          "+"
          («term_^_»
           (Analysis.Normed.Group.Basic.«term‖_‖» "‖" (Term.app `g [`x]) "‖")
           "^"
           (num "2")))]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       `IsROrC.abs
       [(«term_+_»
         («term_^_»
          (Analysis.Normed.Group.Basic.«term‖_‖» "‖" (Term.app `f [`x]) "‖")
          "^"
          (num "2"))
         "+"
         («term_^_»
          (Analysis.Normed.Group.Basic.«term‖_‖» "‖" (Term.app `g [`x]) "‖")
          "^"
          (num "2")))])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_+_»', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_+_»', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_+_»
       («term_^_» (Analysis.Normed.Group.Basic.«term‖_‖» "‖" (Term.app `f [`x]) "‖") "^" (num "2"))
       "+"
       («term_^_» (Analysis.Normed.Group.Basic.«term‖_‖» "‖" (Term.app `g [`x]) "‖") "^" (num "2")))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_^_» (Analysis.Normed.Group.Basic.«term‖_‖» "‖" (Term.app `g [`x]) "‖") "^" (num "2"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (num "2")
[PrettyPrinter.parenthesize] ...precedences are 80 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 80, term))
      (Analysis.Normed.Group.Basic.«term‖_‖» "‖" (Term.app `g [`x]) "‖")
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
[PrettyPrinter.parenthesize] ...precedences are 81 >? 1024, (none, [anonymous]) <=? (some 80, term)
[PrettyPrinter.parenthesize] ...precedences are 66 >? 80, (some 80, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 65, term))
      («term_^_» (Analysis.Normed.Group.Basic.«term‖_‖» "‖" (Term.app `f [`x]) "‖") "^" (num "2"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (num "2")
[PrettyPrinter.parenthesize] ...precedences are 80 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 80, term))
      (Analysis.Normed.Group.Basic.«term‖_‖» "‖" (Term.app `f [`x]) "‖")
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
[PrettyPrinter.parenthesize] ...precedences are 81 >? 1024, (none, [anonymous]) <=? (some 80, term)
[PrettyPrinter.parenthesize] ...precedences are 65 >? 80, (some 80, term) <=? (some 65, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 65, (some 66, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     («term_+_»
      («term_^_» (Analysis.Normed.Group.Basic.«term‖_‖» "‖" (Term.app `f [`x]) "‖") "^" (num "2"))
      "+"
      («term_^_» (Analysis.Normed.Group.Basic.«term‖_‖» "‖" (Term.app `g [`x]) "‖") "^" (num "2")))
     ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `IsROrC.abs
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 50, term))
      (Term.app
       `IsROrC.abs
       [(MeasureTheory.L2Cat.MeasureTheory.Function.L2Space.«term⟪_,_⟫»
         "⟪"
         (Term.app `f [`x])
         ", "
         (Term.app `g [`x])
         "⟫")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'MeasureTheory.L2Cat.MeasureTheory.Function.L2Space.«term⟪_,_⟫»', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'MeasureTheory.L2Cat.MeasureTheory.Function.L2Space.«term⟪_,_⟫»', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (MeasureTheory.L2Cat.MeasureTheory.Function.L2Space.«term⟪_,_⟫»
       "⟪"
       (Term.app `f [`x])
       ", "
       (Term.app `g [`x])
       "⟫")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'MeasureTheory.L2Cat.MeasureTheory.Function.L2Space.«term⟪_,_⟫»', expected 'MeasureTheory.L2Cat.MeasureTheory.Function.L2Space.term⟪_,_⟫._@.MeasureTheory.Function.L2Space._hyg.10'
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
  snorm_inner_lt_top
  ( f g : α →₂[ μ ] E ) : snorm fun x : α => ⟪ f x , g x ⟫ 1 μ < ∞
  :=
    by
      have h : ∀ x , IsROrC.abs ⟪ f x , g x ⟫ ≤ ‖ f x ‖ * ‖ g x ‖ := fun x => abs_inner_le_norm _ _
        have
          h'
            : ∀ x , IsROrC.abs ⟪ f x , g x ⟫ ≤ IsROrC.abs ‖ f x ‖ ^ 2 + ‖ g x ‖ ^ 2
            :=
            by
              refine' fun x => le_trans h x _
                rw [ IsROrC.abs_to_real , abs_eq_self.mpr ]
                swap
                · exact add_nonneg by simp by simp
                refine' le_trans _ half_le_self add_nonneg sq_nonneg _ sq_nonneg _
                refine' le_div_iff zero_lt_two' ℝ . mpr le_of_eq _ . trans two_mul_le_add_sq _ _
                ring
        simp_rw [ ← IsROrC.norm_eq_abs , ← Real.rpow_nat_cast ] at h'
        refine' snorm_mono_ae ae_of_all _ h' . trans_lt snorm_add_le _ _ le_rfl . trans_lt _
        ·
          exact
            Lp.ae_strongly_measurable f . norm . AeMeasurable . pow_const _ . AeStronglyMeasurable
        ·
          exact
            Lp.ae_strongly_measurable g . norm . AeMeasurable . pow_const _ . AeStronglyMeasurable
        simp only [ Nat.cast_bit0 , Ennreal.add_lt_top , Nat.cast_one ]
        exact ⟨ snorm_rpow_two_norm_lt_top f , snorm_rpow_two_norm_lt_top g ⟩
#align measure_theory.L2.snorm_inner_lt_top MeasureTheory.L2Cat.snorm_inner_lt_top

section InnerProductSpace

open ComplexConjugate

include 𝕜

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers [] [] [] [] [] [])
     (Command.instance
      (Term.attrKind [])
      "instance"
      []
      []
      (Command.declSig
       []
       (Term.typeSpec
        ":"
        (Term.app
         `HasInner
         [`𝕜
          (MeasureTheory.MeasureTheory.Function.LpSpace.measure_theory.L2 `α " →₂[" `μ "] " `E)])))
      (Command.declValSimple
       ":="
       (Term.anonymousCtor
        "⟨"
        [(Term.fun
          "fun"
          (Term.basicFun
           [`f `g]
           []
           "=>"
           (MeasureTheory.MeasureTheory.Integral.Bochner.«term∫_,_∂_»
            "∫"
            (Std.ExtendedBinder.extBinders (Std.ExtendedBinder.extBinder (Lean.binderIdent `a) []))
            ", "
            (MeasureTheory.L2Cat.MeasureTheory.Function.L2Space.«term⟪_,_⟫»
             "⟪"
             (Term.app `f [`a])
             ", "
             (Term.app `g [`a])
             "⟫")
            " ∂"
            `μ)))]
        "⟩")
       [])
      []
      []))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.instance', expected 'Lean.Parser.Command.abbrev'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.instance', expected 'Lean.Parser.Command.def'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.instance', expected 'Lean.Parser.Command.theorem'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.instance', expected 'Lean.Parser.Command.opaque'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.anonymousCtor
       "⟨"
       [(Term.fun
         "fun"
         (Term.basicFun
          [`f `g]
          []
          "=>"
          (MeasureTheory.MeasureTheory.Integral.Bochner.«term∫_,_∂_»
           "∫"
           (Std.ExtendedBinder.extBinders (Std.ExtendedBinder.extBinder (Lean.binderIdent `a) []))
           ", "
           (MeasureTheory.L2Cat.MeasureTheory.Function.L2Space.«term⟪_,_⟫»
            "⟪"
            (Term.app `f [`a])
            ", "
            (Term.app `g [`a])
            "⟫")
           " ∂"
           `μ)))]
       "⟩")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.fun
       "fun"
       (Term.basicFun
        [`f `g]
        []
        "=>"
        (MeasureTheory.MeasureTheory.Integral.Bochner.«term∫_,_∂_»
         "∫"
         (Std.ExtendedBinder.extBinders (Std.ExtendedBinder.extBinder (Lean.binderIdent `a) []))
         ", "
         (MeasureTheory.L2Cat.MeasureTheory.Function.L2Space.«term⟪_,_⟫»
          "⟪"
          (Term.app `f [`a])
          ", "
          (Term.app `g [`a])
          "⟫")
         " ∂"
         `μ)))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (MeasureTheory.MeasureTheory.Integral.Bochner.«term∫_,_∂_»
       "∫"
       (Std.ExtendedBinder.extBinders (Std.ExtendedBinder.extBinder (Lean.binderIdent `a) []))
       ", "
       (MeasureTheory.L2Cat.MeasureTheory.Function.L2Space.«term⟪_,_⟫»
        "⟪"
        (Term.app `f [`a])
        ", "
        (Term.app `g [`a])
        "⟫")
       " ∂"
       `μ)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `μ
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (MeasureTheory.L2Cat.MeasureTheory.Function.L2Space.«term⟪_,_⟫»
       "⟪"
       (Term.app `f [`a])
       ", "
       (Term.app `g [`a])
       "⟫")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'MeasureTheory.L2Cat.MeasureTheory.Function.L2Space.«term⟪_,_⟫»', expected 'MeasureTheory.L2Cat.MeasureTheory.Function.L2Space.term⟪_,_⟫._@.MeasureTheory.Function.L2Space._hyg.10'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.basicFun', expected 'Lean.Parser.Term.matchAlts'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.declValSimple', expected 'Lean.Parser.Command.declValEqns'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.declValSimple', expected 'Lean.Parser.Command.whereStructInst'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.instance', expected 'Lean.Parser.Command.axiom'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.instance', expected 'Lean.Parser.Command.example'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.instance', expected 'Lean.Parser.Command.inductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.instance', expected 'Lean.Parser.Command.classInductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.instance', expected 'Lean.Parser.Command.structure'-/-- failed to format: format: uncaught backtrack exception
instance : HasInner 𝕜 α →₂[ μ ] E := ⟨ fun f g => ∫ a , ⟪ f a , g a ⟫ ∂ μ ⟩

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers [] [] [] [] [] [])
     (Command.theorem
      "theorem"
      (Command.declId `inner_def [])
      (Command.declSig
       [(Term.explicitBinder
         "("
         [`f `g]
         [":" (MeasureTheory.MeasureTheory.Function.LpSpace.measure_theory.L2 `α " →₂[" `μ "] " `E)]
         []
         ")")]
       (Term.typeSpec
        ":"
        («term_=_»
         (MeasureTheory.L2Cat.MeasureTheory.Function.L2Space.«term⟪_,_⟫» "⟪" `f ", " `g "⟫")
         "="
         (MeasureTheory.MeasureTheory.Integral.Bochner.«term∫_,_∂_»
          "∫"
          (Std.ExtendedBinder.extBinders
           (Std.ExtendedBinder.extBinder (Lean.binderIdent `a) [(group ":" `α)]))
          ", "
          (MeasureTheory.L2Cat.MeasureTheory.Function.L2Space.«term⟪_,_⟫»
           "⟪"
           (Term.app `f [`a])
           ", "
           (Term.app `g [`a])
           "⟫")
          " ∂"
          `μ))))
      (Command.declValSimple ":=" `rfl [])
      []
      []))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.abbrev'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.def'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `rfl
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
      («term_=_»
       (MeasureTheory.L2Cat.MeasureTheory.Function.L2Space.«term⟪_,_⟫» "⟪" `f ", " `g "⟫")
       "="
       (MeasureTheory.MeasureTheory.Integral.Bochner.«term∫_,_∂_»
        "∫"
        (Std.ExtendedBinder.extBinders
         (Std.ExtendedBinder.extBinder (Lean.binderIdent `a) [(group ":" `α)]))
        ", "
        (MeasureTheory.L2Cat.MeasureTheory.Function.L2Space.«term⟪_,_⟫»
         "⟪"
         (Term.app `f [`a])
         ", "
         (Term.app `g [`a])
         "⟫")
        " ∂"
        `μ))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (MeasureTheory.MeasureTheory.Integral.Bochner.«term∫_,_∂_»
       "∫"
       (Std.ExtendedBinder.extBinders
        (Std.ExtendedBinder.extBinder (Lean.binderIdent `a) [(group ":" `α)]))
       ", "
       (MeasureTheory.L2Cat.MeasureTheory.Function.L2Space.«term⟪_,_⟫»
        "⟪"
        (Term.app `f [`a])
        ", "
        (Term.app `g [`a])
        "⟫")
       " ∂"
       `μ)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `μ
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (MeasureTheory.L2Cat.MeasureTheory.Function.L2Space.«term⟪_,_⟫»
       "⟪"
       (Term.app `f [`a])
       ", "
       (Term.app `g [`a])
       "⟫")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'MeasureTheory.L2Cat.MeasureTheory.Function.L2Space.«term⟪_,_⟫»', expected 'MeasureTheory.L2Cat.MeasureTheory.Function.L2Space.term⟪_,_⟫._@.MeasureTheory.Function.L2Space._hyg.10'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.opaque'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.instance'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.axiom'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.example'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.inductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.classInductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.structure'-/-- failed to format: format: uncaught backtrack exception
theorem inner_def ( f g : α →₂[ μ ] E ) : ⟪ f , g ⟫ = ∫ a : α , ⟪ f a , g a ⟫ ∂ μ := rfl
#align measure_theory.L2.inner_def MeasureTheory.L2Cat.inner_def

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers [] [] [] [] [] [])
     (Command.theorem
      "theorem"
      (Command.declId `integral_inner_eq_sq_snorm [])
      (Command.declSig
       [(Term.explicitBinder
         "("
         [`f]
         [":" (MeasureTheory.MeasureTheory.Function.LpSpace.measure_theory.L2 `α " →₂[" `μ "] " `E)]
         []
         ")")]
       (Term.typeSpec
        ":"
        («term_=_»
         (MeasureTheory.MeasureTheory.Integral.Bochner.«term∫_,_∂_»
          "∫"
          (Std.ExtendedBinder.extBinders (Std.ExtendedBinder.extBinder (Lean.binderIdent `a) []))
          ", "
          (MeasureTheory.L2Cat.MeasureTheory.Function.L2Space.«term⟪_,_⟫»
           "⟪"
           (Term.app `f [`a])
           ", "
           (Term.app `f [`a])
           "⟫")
          " ∂"
          `μ)
         "="
         (Term.app
          `Ennreal.toReal
          [(MeasureTheory.MeasureTheory.Integral.Lebesgue.«term∫⁻_,_∂_»
            "∫⁻"
            (Std.ExtendedBinder.extBinders (Std.ExtendedBinder.extBinder (Lean.binderIdent `a) []))
            ", "
            («term_^_»
             (Term.typeAscription
              "("
              (Analysis.Normed.Group.Basic.«term‖_‖₊» "‖" (Term.app `f [`a]) "‖₊")
              ":"
              [(Ennreal.Data.Real.Ennreal.ennreal "ℝ≥0∞")]
              ")")
             "^"
             (Term.typeAscription "(" (num "2") ":" [(Data.Real.Basic.termℝ "ℝ")] ")"))
            " ∂"
            `μ)]))))
      (Command.declValSimple
       ":="
       (Term.byTactic
        "by"
        (Tactic.tacticSeq
         (Tactic.tacticSeq1Indented
          [(Mathlib.Tactic.tacticSimp_rw__
            "simp_rw"
            (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `inner_self_eq_norm_sq_to_K)] "]")
            [])
           []
           (Tactic.NormCast.tacticNorm_cast__ "norm_cast" [])
           []
           (Tactic.rwSeq
            "rw"
            []
            (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `integral_eq_lintegral_of_nonneg_ae)] "]")
            [])
           []
           (Tactic.rotateLeft "rotate_left" [])
           []
           (tactic__
            (cdotTk (patternIgnore (token.«· » "·")))
            [(Tactic.exact
              "exact"
              (Term.app
               `Filter.eventually_of_forall
               [(Term.fun
                 "fun"
                 (Term.basicFun [`x] [] "=>" (Term.app `sq_nonneg [(Term.hole "_")])))]))])
           []
           (tactic__
            (cdotTk (patternIgnore (token.«· » "·")))
            [(Tactic.exact
              "exact"
              (Term.proj
               (Term.app
                (Term.proj
                 (Term.proj
                  (Term.proj (Term.app `Lp.ae_strongly_measurable [`f]) "." `norm)
                  "."
                  `AeMeasurable)
                 "."
                 `pow_const)
                [(Term.hole "_")])
               "."
               `AeStronglyMeasurable))])
           []
           (Tactic.congr "congr" [])
           []
           (Std.Tactic.Ext.tacticExt1___
            "ext1"
            [(Std.Tactic.RCases.rintroPat.one (Std.Tactic.RCases.rcasesPat.one `x))])
           []
           (Tactic.tacticHave_
            "have"
            (Term.haveDecl
             (Term.haveIdDecl
              [`h_two []]
              [(Term.typeSpec
                ":"
                («term_=_»
                 (Term.typeAscription "(" (num "2") ":" [(Data.Real.Basic.termℝ "ℝ")] ")")
                 "="
                 (Term.typeAscription
                  "("
                  (Term.typeAscription "(" (num "2") ":" [(termℕ "ℕ")] ")")
                  ":"
                  [(Data.Real.Basic.termℝ "ℝ")]
                  ")")))]
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
             [(Tactic.rwRule
               [(patternIgnore (token.«← » "←"))]
               (Term.app `Real.rpow_nat_cast [(Term.hole "_") (num "2")]))
              ","
              (Tactic.rwRule [(patternIgnore (token.«← » "←"))] `h_two)
              ","
              (Tactic.rwRule
               [(patternIgnore (token.«← » "←"))]
               (Term.app
                `Ennreal.of_real_rpow_of_nonneg
                [(Term.app `norm_nonneg [(Term.hole "_")]) `zero_le_two]))
              ","
              (Tactic.rwRule [] `of_real_norm_eq_coe_nnnorm)]
             "]")
            [])
           []
           (Tactic.NormCast.tacticNorm_cast__ "norm_cast" [])])))
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
         [(Mathlib.Tactic.tacticSimp_rw__
           "simp_rw"
           (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `inner_self_eq_norm_sq_to_K)] "]")
           [])
          []
          (Tactic.NormCast.tacticNorm_cast__ "norm_cast" [])
          []
          (Tactic.rwSeq
           "rw"
           []
           (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `integral_eq_lintegral_of_nonneg_ae)] "]")
           [])
          []
          (Tactic.rotateLeft "rotate_left" [])
          []
          (tactic__
           (cdotTk (patternIgnore (token.«· » "·")))
           [(Tactic.exact
             "exact"
             (Term.app
              `Filter.eventually_of_forall
              [(Term.fun
                "fun"
                (Term.basicFun [`x] [] "=>" (Term.app `sq_nonneg [(Term.hole "_")])))]))])
          []
          (tactic__
           (cdotTk (patternIgnore (token.«· » "·")))
           [(Tactic.exact
             "exact"
             (Term.proj
              (Term.app
               (Term.proj
                (Term.proj
                 (Term.proj (Term.app `Lp.ae_strongly_measurable [`f]) "." `norm)
                 "."
                 `AeMeasurable)
                "."
                `pow_const)
               [(Term.hole "_")])
              "."
              `AeStronglyMeasurable))])
          []
          (Tactic.congr "congr" [])
          []
          (Std.Tactic.Ext.tacticExt1___
           "ext1"
           [(Std.Tactic.RCases.rintroPat.one (Std.Tactic.RCases.rcasesPat.one `x))])
          []
          (Tactic.tacticHave_
           "have"
           (Term.haveDecl
            (Term.haveIdDecl
             [`h_two []]
             [(Term.typeSpec
               ":"
               («term_=_»
                (Term.typeAscription "(" (num "2") ":" [(Data.Real.Basic.termℝ "ℝ")] ")")
                "="
                (Term.typeAscription
                 "("
                 (Term.typeAscription "(" (num "2") ":" [(termℕ "ℕ")] ")")
                 ":"
                 [(Data.Real.Basic.termℝ "ℝ")]
                 ")")))]
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
            [(Tactic.rwRule
              [(patternIgnore (token.«← » "←"))]
              (Term.app `Real.rpow_nat_cast [(Term.hole "_") (num "2")]))
             ","
             (Tactic.rwRule [(patternIgnore (token.«← » "←"))] `h_two)
             ","
             (Tactic.rwRule
              [(patternIgnore (token.«← » "←"))]
              (Term.app
               `Ennreal.of_real_rpow_of_nonneg
               [(Term.app `norm_nonneg [(Term.hole "_")]) `zero_le_two]))
             ","
             (Tactic.rwRule [] `of_real_norm_eq_coe_nnnorm)]
            "]")
           [])
          []
          (Tactic.NormCast.tacticNorm_cast__ "norm_cast" [])])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.NormCast.tacticNorm_cast__ "norm_cast" [])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.rwSeq
       "rw"
       []
       (Tactic.rwRuleSeq
        "["
        [(Tactic.rwRule
          [(patternIgnore (token.«← » "←"))]
          (Term.app `Real.rpow_nat_cast [(Term.hole "_") (num "2")]))
         ","
         (Tactic.rwRule [(patternIgnore (token.«← » "←"))] `h_two)
         ","
         (Tactic.rwRule
          [(patternIgnore (token.«← » "←"))]
          (Term.app
           `Ennreal.of_real_rpow_of_nonneg
           [(Term.app `norm_nonneg [(Term.hole "_")]) `zero_le_two]))
         ","
         (Tactic.rwRule [] `of_real_norm_eq_coe_nnnorm)]
        "]")
       [])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `of_real_norm_eq_coe_nnnorm
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       `Ennreal.of_real_rpow_of_nonneg
       [(Term.app `norm_nonneg [(Term.hole "_")]) `zero_le_two])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `zero_le_two
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
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
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023,
     term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.app `norm_nonneg [(Term.hole "_")])
     ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `Ennreal.of_real_rpow_of_nonneg
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `h_two
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `Real.rpow_nat_cast [(Term.hole "_") (num "2")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'num', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'num', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (num "2")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `Real.rpow_nat_cast
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.tacticHave_
       "have"
       (Term.haveDecl
        (Term.haveIdDecl
         [`h_two []]
         [(Term.typeSpec
           ":"
           («term_=_»
            (Term.typeAscription "(" (num "2") ":" [(Data.Real.Basic.termℝ "ℝ")] ")")
            "="
            (Term.typeAscription
             "("
             (Term.typeAscription "(" (num "2") ":" [(termℕ "ℕ")] ")")
             ":"
             [(Data.Real.Basic.termℝ "ℝ")]
             ")")))]
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
      («term_=_»
       (Term.typeAscription "(" (num "2") ":" [(Data.Real.Basic.termℝ "ℝ")] ")")
       "="
       (Term.typeAscription
        "("
        (Term.typeAscription "(" (num "2") ":" [(termℕ "ℕ")] ")")
        ":"
        [(Data.Real.Basic.termℝ "ℝ")]
        ")"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.typeAscription
       "("
       (Term.typeAscription "(" (num "2") ":" [(termℕ "ℕ")] ")")
       ":"
       [(Data.Real.Basic.termℝ "ℝ")]
       ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Data.Real.Basic.termℝ "ℝ")
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.typeAscription "(" (num "2") ":" [(termℕ "ℕ")] ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (termℕ "ℕ")
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (num "2")
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 50, term))
      (Term.typeAscription "(" (num "2") ":" [(Data.Real.Basic.termℝ "ℝ")] ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Data.Real.Basic.termℝ "ℝ")
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (num "2")
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1024, (none, [anonymous]) <=? (some 50, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 50, (some 51, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Std.Tactic.Ext.tacticExt1___
       "ext1"
       [(Std.Tactic.RCases.rintroPat.one (Std.Tactic.RCases.rcasesPat.one `x))])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.congr "congr" [])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (tactic__
       (cdotTk (patternIgnore (token.«· » "·")))
       [(Tactic.exact
         "exact"
         (Term.proj
          (Term.app
           (Term.proj
            (Term.proj
             (Term.proj (Term.app `Lp.ae_strongly_measurable [`f]) "." `norm)
             "."
             `AeMeasurable)
            "."
            `pow_const)
           [(Term.hole "_")])
          "."
          `AeStronglyMeasurable))])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.exact
       "exact"
       (Term.proj
        (Term.app
         (Term.proj
          (Term.proj
           (Term.proj (Term.app `Lp.ae_strongly_measurable [`f]) "." `norm)
           "."
           `AeMeasurable)
          "."
          `pow_const)
         [(Term.hole "_")])
        "."
        `AeStronglyMeasurable))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.proj
       (Term.app
        (Term.proj
         (Term.proj
          (Term.proj (Term.app `Lp.ae_strongly_measurable [`f]) "." `norm)
          "."
          `AeMeasurable)
         "."
         `pow_const)
        [(Term.hole "_")])
       "."
       `AeStronglyMeasurable)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.app
       (Term.proj
        (Term.proj
         (Term.proj (Term.app `Lp.ae_strongly_measurable [`f]) "." `norm)
         "."
         `AeMeasurable)
        "."
        `pow_const)
       [(Term.hole "_")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (Term.proj
       (Term.proj
        (Term.proj (Term.app `Lp.ae_strongly_measurable [`f]) "." `norm)
        "."
        `AeMeasurable)
       "."
       `pow_const)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.proj (Term.proj (Term.app `Lp.ae_strongly_measurable [`f]) "." `norm) "." `AeMeasurable)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.proj (Term.app `Lp.ae_strongly_measurable [`f]) "." `norm)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.app `Lp.ae_strongly_measurable [`f])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `f
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `Lp.ae_strongly_measurable
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.app `Lp.ae_strongly_measurable [`f])
     ")")
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.app
      (Term.proj
       (Term.proj
        (Term.proj (Term.paren "(" (Term.app `Lp.ae_strongly_measurable [`f]) ")") "." `norm)
        "."
        `AeMeasurable)
       "."
       `pow_const)
      [(Term.hole "_")])
     ")")
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (tactic__
       (cdotTk (patternIgnore (token.«· » "·")))
       [(Tactic.exact
         "exact"
         (Term.app
          `Filter.eventually_of_forall
          [(Term.fun
            "fun"
            (Term.basicFun [`x] [] "=>" (Term.app `sq_nonneg [(Term.hole "_")])))]))])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.exact
       "exact"
       (Term.app
        `Filter.eventually_of_forall
        [(Term.fun "fun" (Term.basicFun [`x] [] "=>" (Term.app `sq_nonneg [(Term.hole "_")])))]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       `Filter.eventually_of_forall
       [(Term.fun "fun" (Term.basicFun [`x] [] "=>" (Term.app `sq_nonneg [(Term.hole "_")])))])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.fun "fun" (Term.basicFun [`x] [] "=>" (Term.app `sq_nonneg [(Term.hole "_")])))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `sq_nonneg [(Term.hole "_")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `sq_nonneg
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
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `Filter.eventually_of_forall
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.rotateLeft "rotate_left" [])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.rwSeq
       "rw"
       []
       (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `integral_eq_lintegral_of_nonneg_ae)] "]")
       [])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `integral_eq_lintegral_of_nonneg_ae
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.NormCast.tacticNorm_cast__ "norm_cast" [])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Mathlib.Tactic.tacticSimp_rw__
       "simp_rw"
       (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `inner_self_eq_norm_sq_to_K)] "]")
       [])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `inner_self_eq_norm_sq_to_K
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, tactic) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
      («term_=_»
       (MeasureTheory.MeasureTheory.Integral.Bochner.«term∫_,_∂_»
        "∫"
        (Std.ExtendedBinder.extBinders (Std.ExtendedBinder.extBinder (Lean.binderIdent `a) []))
        ", "
        (MeasureTheory.L2Cat.MeasureTheory.Function.L2Space.«term⟪_,_⟫»
         "⟪"
         (Term.app `f [`a])
         ", "
         (Term.app `f [`a])
         "⟫")
        " ∂"
        `μ)
       "="
       (Term.app
        `Ennreal.toReal
        [(MeasureTheory.MeasureTheory.Integral.Lebesgue.«term∫⁻_,_∂_»
          "∫⁻"
          (Std.ExtendedBinder.extBinders (Std.ExtendedBinder.extBinder (Lean.binderIdent `a) []))
          ", "
          («term_^_»
           (Term.typeAscription
            "("
            (Analysis.Normed.Group.Basic.«term‖_‖₊» "‖" (Term.app `f [`a]) "‖₊")
            ":"
            [(Ennreal.Data.Real.Ennreal.ennreal "ℝ≥0∞")]
            ")")
           "^"
           (Term.typeAscription "(" (num "2") ":" [(Data.Real.Basic.termℝ "ℝ")] ")"))
          " ∂"
          `μ)]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       `Ennreal.toReal
       [(MeasureTheory.MeasureTheory.Integral.Lebesgue.«term∫⁻_,_∂_»
         "∫⁻"
         (Std.ExtendedBinder.extBinders (Std.ExtendedBinder.extBinder (Lean.binderIdent `a) []))
         ", "
         («term_^_»
          (Term.typeAscription
           "("
           (Analysis.Normed.Group.Basic.«term‖_‖₊» "‖" (Term.app `f [`a]) "‖₊")
           ":"
           [(Ennreal.Data.Real.Ennreal.ennreal "ℝ≥0∞")]
           ")")
          "^"
          (Term.typeAscription "(" (num "2") ":" [(Data.Real.Basic.termℝ "ℝ")] ")"))
         " ∂"
         `μ)])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'MeasureTheory.MeasureTheory.Integral.Lebesgue.«term∫⁻_,_∂_»', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'MeasureTheory.MeasureTheory.Integral.Lebesgue.«term∫⁻_,_∂_»', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (MeasureTheory.MeasureTheory.Integral.Lebesgue.«term∫⁻_,_∂_»
       "∫⁻"
       (Std.ExtendedBinder.extBinders (Std.ExtendedBinder.extBinder (Lean.binderIdent `a) []))
       ", "
       («term_^_»
        (Term.typeAscription
         "("
         (Analysis.Normed.Group.Basic.«term‖_‖₊» "‖" (Term.app `f [`a]) "‖₊")
         ":"
         [(Ennreal.Data.Real.Ennreal.ennreal "ℝ≥0∞")]
         ")")
        "^"
        (Term.typeAscription "(" (num "2") ":" [(Data.Real.Basic.termℝ "ℝ")] ")"))
       " ∂"
       `μ)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `μ
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_^_»
       (Term.typeAscription
        "("
        (Analysis.Normed.Group.Basic.«term‖_‖₊» "‖" (Term.app `f [`a]) "‖₊")
        ":"
        [(Ennreal.Data.Real.Ennreal.ennreal "ℝ≥0∞")]
        ")")
       "^"
       (Term.typeAscription "(" (num "2") ":" [(Data.Real.Basic.termℝ "ℝ")] ")"))
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
[PrettyPrinter.parenthesize] ...precedences are 80 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 80, term))
      (Term.typeAscription
       "("
       (Analysis.Normed.Group.Basic.«term‖_‖₊» "‖" (Term.app `f [`a]) "‖₊")
       ":"
       [(Ennreal.Data.Real.Ennreal.ennreal "ℝ≥0∞")]
       ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Ennreal.Data.Real.Ennreal.ennreal "ℝ≥0∞")
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Analysis.Normed.Group.Basic.«term‖_‖₊» "‖" (Term.app `f [`a]) "‖₊")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `f [`a])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `a
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `f
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 81 >? 1024, (none, [anonymous]) <=? (some 80, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 80, (some 80, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (MeasureTheory.MeasureTheory.Integral.Lebesgue.«term∫⁻_,_∂_»
      "∫⁻"
      (Std.ExtendedBinder.extBinders (Std.ExtendedBinder.extBinder (Lean.binderIdent `a) []))
      ", "
      («term_^_»
       (Term.typeAscription
        "("
        (Analysis.Normed.Group.Basic.«term‖_‖₊» "‖" (Term.app `f [`a]) "‖₊")
        ":"
        [(Ennreal.Data.Real.Ennreal.ennreal "ℝ≥0∞")]
        ")")
       "^"
       (Term.typeAscription "(" (num "2") ":" [(Data.Real.Basic.termℝ "ℝ")] ")"))
      " ∂"
      `μ)
     ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `Ennreal.toReal
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 50, term))
      (MeasureTheory.MeasureTheory.Integral.Bochner.«term∫_,_∂_»
       "∫"
       (Std.ExtendedBinder.extBinders (Std.ExtendedBinder.extBinder (Lean.binderIdent `a) []))
       ", "
       (MeasureTheory.L2Cat.MeasureTheory.Function.L2Space.«term⟪_,_⟫»
        "⟪"
        (Term.app `f [`a])
        ", "
        (Term.app `f [`a])
        "⟫")
       " ∂"
       `μ)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `μ
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (MeasureTheory.L2Cat.MeasureTheory.Function.L2Space.«term⟪_,_⟫»
       "⟪"
       (Term.app `f [`a])
       ", "
       (Term.app `f [`a])
       "⟫")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'MeasureTheory.L2Cat.MeasureTheory.Function.L2Space.«term⟪_,_⟫»', expected 'MeasureTheory.L2Cat.MeasureTheory.Function.L2Space.term⟪_,_⟫._@.MeasureTheory.Function.L2Space._hyg.10'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.opaque'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.instance'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.axiom'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.example'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.inductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.classInductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.structure'-/-- failed to format: format: uncaught backtrack exception
theorem
  integral_inner_eq_sq_snorm
  ( f : α →₂[ μ ] E )
    : ∫ a , ⟪ f a , f a ⟫ ∂ μ = Ennreal.toReal ∫⁻ a , ( ‖ f a ‖₊ : ℝ≥0∞ ) ^ ( 2 : ℝ ) ∂ μ
  :=
    by
      simp_rw [ inner_self_eq_norm_sq_to_K ]
        norm_cast
        rw [ integral_eq_lintegral_of_nonneg_ae ]
        rotate_left
        · exact Filter.eventually_of_forall fun x => sq_nonneg _
        ·
          exact
            Lp.ae_strongly_measurable f . norm . AeMeasurable . pow_const _ . AeStronglyMeasurable
        congr
        ext1 x
        have h_two : ( 2 : ℝ ) = ( ( 2 : ℕ ) : ℝ ) := by simp
        rw
          [
            ← Real.rpow_nat_cast _ 2
              ,
              ← h_two
              ,
              ← Ennreal.of_real_rpow_of_nonneg norm_nonneg _ zero_le_two
              ,
              of_real_norm_eq_coe_nnnorm
            ]
        norm_cast
#align measure_theory.L2.integral_inner_eq_sq_snorm MeasureTheory.L2Cat.integral_inner_eq_sq_snorm

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers [] [] [(Command.private "private")] [] [] [])
     (Command.theorem
      "theorem"
      (Command.declId `norm_sq_eq_inner' [])
      (Command.declSig
       [(Term.explicitBinder
         "("
         [`f]
         [":" (MeasureTheory.MeasureTheory.Function.LpSpace.measure_theory.L2 `α " →₂[" `μ "] " `E)]
         []
         ")")]
       (Term.typeSpec
        ":"
        («term_=_»
         («term_^_» (Analysis.Normed.Group.Basic.«term‖_‖» "‖" `f "‖") "^" (num "2"))
         "="
         (Term.app
          `IsROrC.re
          [(MeasureTheory.L2Cat.MeasureTheory.Function.L2Space.«term⟪_,_⟫» "⟪" `f ", " `f "⟫")]))))
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
              [`h_two []]
              [(Term.typeSpec
                ":"
                («term_=_»
                 (Term.proj
                  (Term.typeAscription
                   "("
                   (num "2")
                   ":"
                   [(Ennreal.Data.Real.Ennreal.ennreal "ℝ≥0∞")]
                   ")")
                  "."
                  `toReal)
                 "="
                 (num "2")))]
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
             [(Tactic.rwRule [] `inner_def)
              ","
              (Tactic.rwRule [] `integral_inner_eq_sq_snorm)
              ","
              (Tactic.rwRule [] `norm_def)
              ","
              (Tactic.rwRule [(patternIgnore (token.«← » "←"))] `Ennreal.to_real_pow)
              ","
              (Tactic.rwRule [] `IsROrC.of_real_re)
              ","
              (Tactic.rwRule
               []
               (Term.app
                `Ennreal.to_real_eq_to_real
                [(Term.app `Ennreal.pow_ne_top [(Term.app `Lp.snorm_ne_top [`f])])
                 (Term.hole "_")]))]
             "]")
            [])
           []
           (tactic__
            (cdotTk (patternIgnore (token.«· » "·")))
            [(Tactic.rwSeq
              "rw"
              []
              (Tactic.rwRuleSeq
               "["
               [(Tactic.rwRule [(patternIgnore (token.«← » "←"))] `Ennreal.rpow_nat_cast)
                ","
                (Tactic.rwRule
                 []
                 (Term.app `snorm_eq_snorm' [`Ennreal.two_ne_zero `Ennreal.two_ne_top]))
                ","
                (Tactic.rwRule [] `snorm')
                ","
                (Tactic.rwRule [(patternIgnore (token.«← » "←"))] `Ennreal.rpow_mul)
                ","
                (Tactic.rwRule [] `one_div)
                ","
                (Tactic.rwRule [] `h_two)]
               "]")
              [])
             []
             (Tactic.simp "simp" [] [] [] [] [])])
           []
           (tactic__
            (cdotTk (patternIgnore (token.«· » "·")))
            [(Tactic.refine'
              "refine'"
              (Term.proj
               (Term.app
                `lintegral_rpow_nnnorm_lt_top_of_snorm'_lt_top
                [`zero_lt_two (Term.hole "_")])
               "."
               `Ne))
             []
             (Tactic.rwSeq
              "rw"
              []
              (Tactic.rwRuleSeq
               "["
               [(Tactic.rwRule [(patternIgnore (token.«← » "←"))] `h_two)
                ","
                (Tactic.rwRule
                 [(patternIgnore (token.«← » "←"))]
                 (Term.app `snorm_eq_snorm' [`Ennreal.two_ne_zero `Ennreal.two_ne_top]))]
               "]")
              [])
             []
             (Tactic.exact "exact" (Term.app `Lp.snorm_lt_top [`f]))])])))
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
             [`h_two []]
             [(Term.typeSpec
               ":"
               («term_=_»
                (Term.proj
                 (Term.typeAscription
                  "("
                  (num "2")
                  ":"
                  [(Ennreal.Data.Real.Ennreal.ennreal "ℝ≥0∞")]
                  ")")
                 "."
                 `toReal)
                "="
                (num "2")))]
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
            [(Tactic.rwRule [] `inner_def)
             ","
             (Tactic.rwRule [] `integral_inner_eq_sq_snorm)
             ","
             (Tactic.rwRule [] `norm_def)
             ","
             (Tactic.rwRule [(patternIgnore (token.«← » "←"))] `Ennreal.to_real_pow)
             ","
             (Tactic.rwRule [] `IsROrC.of_real_re)
             ","
             (Tactic.rwRule
              []
              (Term.app
               `Ennreal.to_real_eq_to_real
               [(Term.app `Ennreal.pow_ne_top [(Term.app `Lp.snorm_ne_top [`f])])
                (Term.hole "_")]))]
            "]")
           [])
          []
          (tactic__
           (cdotTk (patternIgnore (token.«· » "·")))
           [(Tactic.rwSeq
             "rw"
             []
             (Tactic.rwRuleSeq
              "["
              [(Tactic.rwRule [(patternIgnore (token.«← » "←"))] `Ennreal.rpow_nat_cast)
               ","
               (Tactic.rwRule
                []
                (Term.app `snorm_eq_snorm' [`Ennreal.two_ne_zero `Ennreal.two_ne_top]))
               ","
               (Tactic.rwRule [] `snorm')
               ","
               (Tactic.rwRule [(patternIgnore (token.«← » "←"))] `Ennreal.rpow_mul)
               ","
               (Tactic.rwRule [] `one_div)
               ","
               (Tactic.rwRule [] `h_two)]
              "]")
             [])
            []
            (Tactic.simp "simp" [] [] [] [] [])])
          []
          (tactic__
           (cdotTk (patternIgnore (token.«· » "·")))
           [(Tactic.refine'
             "refine'"
             (Term.proj
              (Term.app
               `lintegral_rpow_nnnorm_lt_top_of_snorm'_lt_top
               [`zero_lt_two (Term.hole "_")])
              "."
              `Ne))
            []
            (Tactic.rwSeq
             "rw"
             []
             (Tactic.rwRuleSeq
              "["
              [(Tactic.rwRule [(patternIgnore (token.«← » "←"))] `h_two)
               ","
               (Tactic.rwRule
                [(patternIgnore (token.«← » "←"))]
                (Term.app `snorm_eq_snorm' [`Ennreal.two_ne_zero `Ennreal.two_ne_top]))]
              "]")
             [])
            []
            (Tactic.exact "exact" (Term.app `Lp.snorm_lt_top [`f]))])])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (tactic__
       (cdotTk (patternIgnore (token.«· » "·")))
       [(Tactic.refine'
         "refine'"
         (Term.proj
          (Term.app `lintegral_rpow_nnnorm_lt_top_of_snorm'_lt_top [`zero_lt_two (Term.hole "_")])
          "."
          `Ne))
        []
        (Tactic.rwSeq
         "rw"
         []
         (Tactic.rwRuleSeq
          "["
          [(Tactic.rwRule [(patternIgnore (token.«← » "←"))] `h_two)
           ","
           (Tactic.rwRule
            [(patternIgnore (token.«← » "←"))]
            (Term.app `snorm_eq_snorm' [`Ennreal.two_ne_zero `Ennreal.two_ne_top]))]
          "]")
         [])
        []
        (Tactic.exact "exact" (Term.app `Lp.snorm_lt_top [`f]))])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.exact "exact" (Term.app `Lp.snorm_lt_top [`f]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `Lp.snorm_lt_top [`f])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `f
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `Lp.snorm_lt_top
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
        [(Tactic.rwRule [(patternIgnore (token.«← » "←"))] `h_two)
         ","
         (Tactic.rwRule
          [(patternIgnore (token.«← » "←"))]
          (Term.app `snorm_eq_snorm' [`Ennreal.two_ne_zero `Ennreal.two_ne_top]))]
        "]")
       [])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `snorm_eq_snorm' [`Ennreal.two_ne_zero `Ennreal.two_ne_top])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `Ennreal.two_ne_top
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `Ennreal.two_ne_zero
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `snorm_eq_snorm'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `h_two
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.refine'
       "refine'"
       (Term.proj
        (Term.app `lintegral_rpow_nnnorm_lt_top_of_snorm'_lt_top [`zero_lt_two (Term.hole "_")])
        "."
        `Ne))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.proj
       (Term.app `lintegral_rpow_nnnorm_lt_top_of_snorm'_lt_top [`zero_lt_two (Term.hole "_")])
       "."
       `Ne)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.app `lintegral_rpow_nnnorm_lt_top_of_snorm'_lt_top [`zero_lt_two (Term.hole "_")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, term))
      `zero_lt_two
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1023, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `lintegral_rpow_nnnorm_lt_top_of_snorm'_lt_top
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.app `lintegral_rpow_nnnorm_lt_top_of_snorm'_lt_top [`zero_lt_two (Term.hole "_")])
     ")")
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
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
          [(Tactic.rwRule [(patternIgnore (token.«← » "←"))] `Ennreal.rpow_nat_cast)
           ","
           (Tactic.rwRule [] (Term.app `snorm_eq_snorm' [`Ennreal.two_ne_zero `Ennreal.two_ne_top]))
           ","
           (Tactic.rwRule [] `snorm')
           ","
           (Tactic.rwRule [(patternIgnore (token.«← » "←"))] `Ennreal.rpow_mul)
           ","
           (Tactic.rwRule [] `one_div)
           ","
           (Tactic.rwRule [] `h_two)]
          "]")
         [])
        []
        (Tactic.simp "simp" [] [] [] [] [])])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.simp "simp" [] [] [] [] [])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.rwSeq
       "rw"
       []
       (Tactic.rwRuleSeq
        "["
        [(Tactic.rwRule [(patternIgnore (token.«← » "←"))] `Ennreal.rpow_nat_cast)
         ","
         (Tactic.rwRule [] (Term.app `snorm_eq_snorm' [`Ennreal.two_ne_zero `Ennreal.two_ne_top]))
         ","
         (Tactic.rwRule [] `snorm')
         ","
         (Tactic.rwRule [(patternIgnore (token.«← » "←"))] `Ennreal.rpow_mul)
         ","
         (Tactic.rwRule [] `one_div)
         ","
         (Tactic.rwRule [] `h_two)]
        "]")
       [])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `h_two
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `one_div
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `Ennreal.rpow_mul
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `snorm'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `snorm_eq_snorm' [`Ennreal.two_ne_zero `Ennreal.two_ne_top])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `Ennreal.two_ne_top
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `Ennreal.two_ne_zero
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `snorm_eq_snorm'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `Ennreal.rpow_nat_cast
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.rwSeq
       "rw"
       []
       (Tactic.rwRuleSeq
        "["
        [(Tactic.rwRule [] `inner_def)
         ","
         (Tactic.rwRule [] `integral_inner_eq_sq_snorm)
         ","
         (Tactic.rwRule [] `norm_def)
         ","
         (Tactic.rwRule [(patternIgnore (token.«← » "←"))] `Ennreal.to_real_pow)
         ","
         (Tactic.rwRule [] `IsROrC.of_real_re)
         ","
         (Tactic.rwRule
          []
          (Term.app
           `Ennreal.to_real_eq_to_real
           [(Term.app `Ennreal.pow_ne_top [(Term.app `Lp.snorm_ne_top [`f])]) (Term.hole "_")]))]
        "]")
       [])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       `Ennreal.to_real_eq_to_real
       [(Term.app `Ennreal.pow_ne_top [(Term.app `Lp.snorm_ne_top [`f])]) (Term.hole "_")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, term))
      (Term.app `Ennreal.pow_ne_top [(Term.app `Lp.snorm_ne_top [`f])])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `Lp.snorm_ne_top [`f])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `f
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `Lp.snorm_ne_top
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren "(" (Term.app `Lp.snorm_ne_top [`f]) ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `Ennreal.pow_ne_top
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023,
     term) <=? (some 1023, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.app `Ennreal.pow_ne_top [(Term.paren "(" (Term.app `Lp.snorm_ne_top [`f]) ")")])
     ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `Ennreal.to_real_eq_to_real
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `IsROrC.of_real_re
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `Ennreal.to_real_pow
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `norm_def
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `integral_inner_eq_sq_snorm
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `inner_def
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.tacticHave_
       "have"
       (Term.haveDecl
        (Term.haveIdDecl
         [`h_two []]
         [(Term.typeSpec
           ":"
           («term_=_»
            (Term.proj
             (Term.typeAscription
              "("
              (num "2")
              ":"
              [(Ennreal.Data.Real.Ennreal.ennreal "ℝ≥0∞")]
              ")")
             "."
             `toReal)
            "="
            (num "2")))]
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
      («term_=_»
       (Term.proj
        (Term.typeAscription "(" (num "2") ":" [(Ennreal.Data.Real.Ennreal.ennreal "ℝ≥0∞")] ")")
        "."
        `toReal)
       "="
       (num "2"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (num "2")
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 50, term))
      (Term.proj
       (Term.typeAscription "(" (num "2") ":" [(Ennreal.Data.Real.Ennreal.ennreal "ℝ≥0∞")] ")")
       "."
       `toReal)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.typeAscription "(" (num "2") ":" [(Ennreal.Data.Real.Ennreal.ennreal "ℝ≥0∞")] ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Ennreal.Data.Real.Ennreal.ennreal "ℝ≥0∞")
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (num "2")
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1024, (none, [anonymous]) <=? (some 50, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 50, (some 51, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, tactic) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
      («term_=_»
       («term_^_» (Analysis.Normed.Group.Basic.«term‖_‖» "‖" `f "‖") "^" (num "2"))
       "="
       (Term.app
        `IsROrC.re
        [(MeasureTheory.L2Cat.MeasureTheory.Function.L2Space.«term⟪_,_⟫» "⟪" `f ", " `f "⟫")]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       `IsROrC.re
       [(MeasureTheory.L2Cat.MeasureTheory.Function.L2Space.«term⟪_,_⟫» "⟪" `f ", " `f "⟫")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'MeasureTheory.L2Cat.MeasureTheory.Function.L2Space.«term⟪_,_⟫»', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'MeasureTheory.L2Cat.MeasureTheory.Function.L2Space.«term⟪_,_⟫»', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (MeasureTheory.L2Cat.MeasureTheory.Function.L2Space.«term⟪_,_⟫» "⟪" `f ", " `f "⟫")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'MeasureTheory.L2Cat.MeasureTheory.Function.L2Space.«term⟪_,_⟫»', expected 'MeasureTheory.L2Cat.MeasureTheory.Function.L2Space.term⟪_,_⟫._@.MeasureTheory.Function.L2Space._hyg.10'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.opaque'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.instance'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.axiom'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.example'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.inductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.classInductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.structure'-/-- failed to format: format: uncaught backtrack exception
private
  theorem
    norm_sq_eq_inner'
    ( f : α →₂[ μ ] E ) : ‖ f ‖ ^ 2 = IsROrC.re ⟪ f , f ⟫
    :=
      by
        have h_two : ( 2 : ℝ≥0∞ ) . toReal = 2 := by simp
          rw
            [
              inner_def
                ,
                integral_inner_eq_sq_snorm
                ,
                norm_def
                ,
                ← Ennreal.to_real_pow
                ,
                IsROrC.of_real_re
                ,
                Ennreal.to_real_eq_to_real Ennreal.pow_ne_top Lp.snorm_ne_top f _
              ]
          ·
            rw
                [
                  ← Ennreal.rpow_nat_cast
                    ,
                    snorm_eq_snorm' Ennreal.two_ne_zero Ennreal.two_ne_top
                    ,
                    snorm'
                    ,
                    ← Ennreal.rpow_mul
                    ,
                    one_div
                    ,
                    h_two
                  ]
              simp
          ·
            refine' lintegral_rpow_nnnorm_lt_top_of_snorm'_lt_top zero_lt_two _ . Ne
              rw [ ← h_two , ← snorm_eq_snorm' Ennreal.two_ne_zero Ennreal.two_ne_top ]
              exact Lp.snorm_lt_top f
#align measure_theory.L2.norm_sq_eq_inner' measure_theory.L2.norm_sq_eq_inner'

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers [] [] [] [] [] [])
     (Command.theorem
      "theorem"
      (Command.declId `mem_L1_inner [])
      (Command.declSig
       [(Term.explicitBinder
         "("
         [`f `g]
         [":" (MeasureTheory.MeasureTheory.Function.LpSpace.measure_theory.L2 `α " →₂[" `μ "] " `E)]
         []
         ")")]
       (Term.typeSpec
        ":"
        («term_∈_»
         (Term.app
          `AeEqFun.mk
          [(Term.fun
            "fun"
            (Term.basicFun
             [`x]
             []
             "=>"
             (MeasureTheory.L2Cat.MeasureTheory.Function.L2Space.«term⟪_,_⟫»
              "⟪"
              (Term.app `f [`x])
              ", "
              (Term.app `g [`x])
              "⟫")))
           (Term.app
            (Term.proj (Term.app `lp.aeStronglyMeasurable [`f]) "." `inner)
            [(Term.app `lp.aeStronglyMeasurable [`g])])])
         "∈"
         (Term.app `lp [`𝕜 (num "1") `μ]))))
      (Command.declValSimple
       ":="
       (Term.byTactic
        "by"
        (Tactic.tacticSeq
         (Tactic.tacticSeq1Indented
          [(Mathlib.Tactic.tacticSimp_rw__
            "simp_rw"
            (Tactic.rwRuleSeq
             "["
             [(Tactic.rwRule [] `mem_Lp_iff_snorm_lt_top) "," (Tactic.rwRule [] `snorm_ae_eq_fun)]
             "]")
            [])
           []
           (Tactic.exact "exact" (Term.app `snorm_inner_lt_top [`f `g]))])))
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
         [(Mathlib.Tactic.tacticSimp_rw__
           "simp_rw"
           (Tactic.rwRuleSeq
            "["
            [(Tactic.rwRule [] `mem_Lp_iff_snorm_lt_top) "," (Tactic.rwRule [] `snorm_ae_eq_fun)]
            "]")
           [])
          []
          (Tactic.exact "exact" (Term.app `snorm_inner_lt_top [`f `g]))])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.exact "exact" (Term.app `snorm_inner_lt_top [`f `g]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `snorm_inner_lt_top [`f `g])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `g
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `f
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `snorm_inner_lt_top
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Mathlib.Tactic.tacticSimp_rw__
       "simp_rw"
       (Tactic.rwRuleSeq
        "["
        [(Tactic.rwRule [] `mem_Lp_iff_snorm_lt_top) "," (Tactic.rwRule [] `snorm_ae_eq_fun)]
        "]")
       [])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `snorm_ae_eq_fun
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `mem_Lp_iff_snorm_lt_top
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, tactic) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
      («term_∈_»
       (Term.app
        `AeEqFun.mk
        [(Term.fun
          "fun"
          (Term.basicFun
           [`x]
           []
           "=>"
           (MeasureTheory.L2Cat.MeasureTheory.Function.L2Space.«term⟪_,_⟫»
            "⟪"
            (Term.app `f [`x])
            ", "
            (Term.app `g [`x])
            "⟫")))
         (Term.app
          (Term.proj (Term.app `lp.aeStronglyMeasurable [`f]) "." `inner)
          [(Term.app `lp.aeStronglyMeasurable [`g])])])
       "∈"
       (Term.app `lp [`𝕜 (num "1") `μ]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `lp [`𝕜 (num "1") `μ])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `μ
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'num', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'num', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (num "1")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `𝕜
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `lp
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 50, term))
      (Term.app
       `AeEqFun.mk
       [(Term.fun
         "fun"
         (Term.basicFun
          [`x]
          []
          "=>"
          (MeasureTheory.L2Cat.MeasureTheory.Function.L2Space.«term⟪_,_⟫»
           "⟪"
           (Term.app `f [`x])
           ", "
           (Term.app `g [`x])
           "⟫")))
        (Term.app
         (Term.proj (Term.app `lp.aeStronglyMeasurable [`f]) "." `inner)
         [(Term.app `lp.aeStronglyMeasurable [`g])])])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       (Term.proj (Term.app `lp.aeStronglyMeasurable [`f]) "." `inner)
       [(Term.app `lp.aeStronglyMeasurable [`g])])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `lp.aeStronglyMeasurable [`g])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `g
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `lp.aeStronglyMeasurable
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.app `lp.aeStronglyMeasurable [`g])
     ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (Term.proj (Term.app `lp.aeStronglyMeasurable [`f]) "." `inner)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.app `lp.aeStronglyMeasurable [`f])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `f
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `lp.aeStronglyMeasurable
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.app `lp.aeStronglyMeasurable [`f])
     ")")
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.app
      (Term.proj (Term.paren "(" (Term.app `lp.aeStronglyMeasurable [`f]) ")") "." `inner)
      [(Term.paren "(" (Term.app `lp.aeStronglyMeasurable [`g]) ")")])
     ")")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.fun
       "fun"
       (Term.basicFun
        [`x]
        []
        "=>"
        (MeasureTheory.L2Cat.MeasureTheory.Function.L2Space.«term⟪_,_⟫»
         "⟪"
         (Term.app `f [`x])
         ", "
         (Term.app `g [`x])
         "⟫")))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (MeasureTheory.L2Cat.MeasureTheory.Function.L2Space.«term⟪_,_⟫»
       "⟪"
       (Term.app `f [`x])
       ", "
       (Term.app `g [`x])
       "⟫")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'MeasureTheory.L2Cat.MeasureTheory.Function.L2Space.«term⟪_,_⟫»', expected 'MeasureTheory.L2Cat.MeasureTheory.Function.L2Space.term⟪_,_⟫._@.MeasureTheory.Function.L2Space._hyg.10'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.basicFun', expected 'Lean.Parser.Term.matchAlts'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.opaque'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.instance'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.axiom'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.example'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.inductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.classInductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.structure'-/-- failed to format: format: uncaught backtrack exception
theorem
  mem_L1_inner
  ( f g : α →₂[ μ ] E )
    :
      AeEqFun.mk fun x => ⟪ f x , g x ⟫ lp.aeStronglyMeasurable f . inner lp.aeStronglyMeasurable g
        ∈
        lp 𝕜 1 μ
  := by simp_rw [ mem_Lp_iff_snorm_lt_top , snorm_ae_eq_fun ] exact snorm_inner_lt_top f g
#align measure_theory.L2.mem_L1_inner MeasureTheory.L2Cat.mem_L1_inner

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers [] [] [] [] [] [])
     (Command.theorem
      "theorem"
      (Command.declId `integrableInner [])
      (Command.declSig
       [(Term.explicitBinder
         "("
         [`f `g]
         [":" (MeasureTheory.MeasureTheory.Function.LpSpace.measure_theory.L2 `α " →₂[" `μ "] " `E)]
         []
         ")")]
       (Term.typeSpec
        ":"
        (Term.app
         `Integrable
         [(Term.fun
           "fun"
           (Term.basicFun
            [`x]
            [(Term.typeSpec ":" `α)]
            "=>"
            (MeasureTheory.L2Cat.MeasureTheory.Function.L2Space.«term⟪_,_⟫»
             "⟪"
             (Term.app `f [`x])
             ", "
             (Term.app `g [`x])
             "⟫")))
          `μ])))
      (Command.declValSimple
       ":="
       (Term.app
        (Term.proj
         (Term.app
          `integrable_congr
          [(Term.app
            `AeEqFun.coe_fn_mk
            [(Term.fun
              "fun"
              (Term.basicFun
               [`x]
               []
               "=>"
               (MeasureTheory.L2Cat.MeasureTheory.Function.L2Space.«term⟪_,_⟫»
                "⟪"
                (Term.app `f [`x])
                ", "
                (Term.app `g [`x])
                "⟫")))
             (Term.app
              (Term.proj (Term.app `lp.aeStronglyMeasurable [`f]) "." `inner)
              [(Term.app `lp.aeStronglyMeasurable [`g])])])])
         "."
         `mp)
        [(Term.app
          (Term.proj `AeEqFun.integrable_iff_mem_L1 "." `mpr)
          [(Term.app `mem_L1_inner [`f `g])])])
       [])
      []
      []))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.abbrev'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.def'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       (Term.proj
        (Term.app
         `integrable_congr
         [(Term.app
           `AeEqFun.coe_fn_mk
           [(Term.fun
             "fun"
             (Term.basicFun
              [`x]
              []
              "=>"
              (MeasureTheory.L2Cat.MeasureTheory.Function.L2Space.«term⟪_,_⟫»
               "⟪"
               (Term.app `f [`x])
               ", "
               (Term.app `g [`x])
               "⟫")))
            (Term.app
             (Term.proj (Term.app `lp.aeStronglyMeasurable [`f]) "." `inner)
             [(Term.app `lp.aeStronglyMeasurable [`g])])])])
        "."
        `mp)
       [(Term.app
         (Term.proj `AeEqFun.integrable_iff_mem_L1 "." `mpr)
         [(Term.app `mem_L1_inner [`f `g])])])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       (Term.proj `AeEqFun.integrable_iff_mem_L1 "." `mpr)
       [(Term.app `mem_L1_inner [`f `g])])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `mem_L1_inner [`f `g])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `g
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `f
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `mem_L1_inner
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren "(" (Term.app `mem_L1_inner [`f `g]) ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (Term.proj `AeEqFun.integrable_iff_mem_L1 "." `mpr)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `AeEqFun.integrable_iff_mem_L1
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.app
      (Term.proj `AeEqFun.integrable_iff_mem_L1 "." `mpr)
      [(Term.paren "(" (Term.app `mem_L1_inner [`f `g]) ")")])
     ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (Term.proj
       (Term.app
        `integrable_congr
        [(Term.app
          `AeEqFun.coe_fn_mk
          [(Term.fun
            "fun"
            (Term.basicFun
             [`x]
             []
             "=>"
             (MeasureTheory.L2Cat.MeasureTheory.Function.L2Space.«term⟪_,_⟫»
              "⟪"
              (Term.app `f [`x])
              ", "
              (Term.app `g [`x])
              "⟫")))
           (Term.app
            (Term.proj (Term.app `lp.aeStronglyMeasurable [`f]) "." `inner)
            [(Term.app `lp.aeStronglyMeasurable [`g])])])])
       "."
       `mp)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.app
       `integrable_congr
       [(Term.app
         `AeEqFun.coe_fn_mk
         [(Term.fun
           "fun"
           (Term.basicFun
            [`x]
            []
            "=>"
            (MeasureTheory.L2Cat.MeasureTheory.Function.L2Space.«term⟪_,_⟫»
             "⟪"
             (Term.app `f [`x])
             ", "
             (Term.app `g [`x])
             "⟫")))
          (Term.app
           (Term.proj (Term.app `lp.aeStronglyMeasurable [`f]) "." `inner)
           [(Term.app `lp.aeStronglyMeasurable [`g])])])])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       `AeEqFun.coe_fn_mk
       [(Term.fun
         "fun"
         (Term.basicFun
          [`x]
          []
          "=>"
          (MeasureTheory.L2Cat.MeasureTheory.Function.L2Space.«term⟪_,_⟫»
           "⟪"
           (Term.app `f [`x])
           ", "
           (Term.app `g [`x])
           "⟫")))
        (Term.app
         (Term.proj (Term.app `lp.aeStronglyMeasurable [`f]) "." `inner)
         [(Term.app `lp.aeStronglyMeasurable [`g])])])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       (Term.proj (Term.app `lp.aeStronglyMeasurable [`f]) "." `inner)
       [(Term.app `lp.aeStronglyMeasurable [`g])])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `lp.aeStronglyMeasurable [`g])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `g
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `lp.aeStronglyMeasurable
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.app `lp.aeStronglyMeasurable [`g])
     ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (Term.proj (Term.app `lp.aeStronglyMeasurable [`f]) "." `inner)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.app `lp.aeStronglyMeasurable [`f])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `f
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `lp.aeStronglyMeasurable
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.app `lp.aeStronglyMeasurable [`f])
     ")")
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.app
      (Term.proj (Term.paren "(" (Term.app `lp.aeStronglyMeasurable [`f]) ")") "." `inner)
      [(Term.paren "(" (Term.app `lp.aeStronglyMeasurable [`g]) ")")])
     ")")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.fun
       "fun"
       (Term.basicFun
        [`x]
        []
        "=>"
        (MeasureTheory.L2Cat.MeasureTheory.Function.L2Space.«term⟪_,_⟫»
         "⟪"
         (Term.app `f [`x])
         ", "
         (Term.app `g [`x])
         "⟫")))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (MeasureTheory.L2Cat.MeasureTheory.Function.L2Space.«term⟪_,_⟫»
       "⟪"
       (Term.app `f [`x])
       ", "
       (Term.app `g [`x])
       "⟫")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'MeasureTheory.L2Cat.MeasureTheory.Function.L2Space.«term⟪_,_⟫»', expected 'MeasureTheory.L2Cat.MeasureTheory.Function.L2Space.term⟪_,_⟫._@.MeasureTheory.Function.L2Space._hyg.10'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.basicFun', expected 'Lean.Parser.Term.matchAlts'
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
  integrableInner
  ( f g : α →₂[ μ ] E ) : Integrable fun x : α => ⟪ f x , g x ⟫ μ
  :=
    integrable_congr
          AeEqFun.coe_fn_mk
            fun x => ⟪ f x , g x ⟫ lp.aeStronglyMeasurable f . inner lp.aeStronglyMeasurable g
        .
        mp
      AeEqFun.integrable_iff_mem_L1 . mpr mem_L1_inner f g
#align measure_theory.L2.integrable_inner MeasureTheory.L2Cat.integrableInner

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers [] [] [(Command.private "private")] [] [] [])
     (Command.theorem
      "theorem"
      (Command.declId `add_left' [])
      (Command.declSig
       [(Term.explicitBinder
         "("
         [`f `f' `g]
         [":" (MeasureTheory.MeasureTheory.Function.LpSpace.measure_theory.L2 `α " →₂[" `μ "] " `E)]
         []
         ")")]
       (Term.typeSpec
        ":"
        («term_=_»
         (MeasureTheory.L2Cat.MeasureTheory.Function.L2Space.«term⟪_,_⟫»
          "⟪"
          («term_+_» `f "+" `f')
          ", "
          `g
          "⟫")
         "="
         («term_+_» (Term.app `inner [`f `g]) "+" (Term.app `inner [`f' `g])))))
      (Command.declValSimple
       ":="
       (Term.byTactic
        "by"
        (Tactic.tacticSeq
         (Tactic.tacticSeq1Indented
          [(Mathlib.Tactic.tacticSimp_rw__
            "simp_rw"
            (Tactic.rwRuleSeq
             "["
             [(Tactic.rwRule [] `inner_def)
              ","
              (Tactic.rwRule
               [(patternIgnore (token.«← » "←"))]
               (Term.app
                `integral_add
                [(Term.app `integrable_inner [`f `g]) (Term.app `integrable_inner [`f' `g])]))
              ","
              (Tactic.rwRule [(patternIgnore (token.«← » "←"))] `inner_add_left)]
             "]")
            [])
           []
           (Tactic.refine'
            "refine'"
            (Term.app
             `integral_congr_ae
             [(Term.app
               (Term.proj (Term.app `coe_fn_add [`f `f']) "." `mono)
               [(Term.fun "fun" (Term.basicFun [`x `hx] [] "=>" (Term.hole "_")))])]))
           []
           (Tactic.congr "congr" [])
           []
           (Std.Tactic.tacticRwa__
            "rwa"
            (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `Pi.add_apply)] "]")
            [(Tactic.location "at" (Tactic.locationHyp [`hx] []))])])))
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
         [(Mathlib.Tactic.tacticSimp_rw__
           "simp_rw"
           (Tactic.rwRuleSeq
            "["
            [(Tactic.rwRule [] `inner_def)
             ","
             (Tactic.rwRule
              [(patternIgnore (token.«← » "←"))]
              (Term.app
               `integral_add
               [(Term.app `integrable_inner [`f `g]) (Term.app `integrable_inner [`f' `g])]))
             ","
             (Tactic.rwRule [(patternIgnore (token.«← » "←"))] `inner_add_left)]
            "]")
           [])
          []
          (Tactic.refine'
           "refine'"
           (Term.app
            `integral_congr_ae
            [(Term.app
              (Term.proj (Term.app `coe_fn_add [`f `f']) "." `mono)
              [(Term.fun "fun" (Term.basicFun [`x `hx] [] "=>" (Term.hole "_")))])]))
          []
          (Tactic.congr "congr" [])
          []
          (Std.Tactic.tacticRwa__
           "rwa"
           (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `Pi.add_apply)] "]")
           [(Tactic.location "at" (Tactic.locationHyp [`hx] []))])])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Std.Tactic.tacticRwa__
       "rwa"
       (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `Pi.add_apply)] "]")
       [(Tactic.location "at" (Tactic.locationHyp [`hx] []))])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.locationHyp', expected 'Lean.Parser.Tactic.locationWildcard'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `hx
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `Pi.add_apply
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.congr "congr" [])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.refine'
       "refine'"
       (Term.app
        `integral_congr_ae
        [(Term.app
          (Term.proj (Term.app `coe_fn_add [`f `f']) "." `mono)
          [(Term.fun "fun" (Term.basicFun [`x `hx] [] "=>" (Term.hole "_")))])]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       `integral_congr_ae
       [(Term.app
         (Term.proj (Term.app `coe_fn_add [`f `f']) "." `mono)
         [(Term.fun "fun" (Term.basicFun [`x `hx] [] "=>" (Term.hole "_")))])])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       (Term.proj (Term.app `coe_fn_add [`f `f']) "." `mono)
       [(Term.fun "fun" (Term.basicFun [`x `hx] [] "=>" (Term.hole "_")))])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.fun "fun" (Term.basicFun [`x `hx] [] "=>" (Term.hole "_")))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
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
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (Term.proj (Term.app `coe_fn_add [`f `f']) "." `mono)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.app `coe_fn_add [`f `f'])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `f'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `f
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `coe_fn_add
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren "(" (Term.app `coe_fn_add [`f `f']) ")")
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.app
      (Term.proj (Term.paren "(" (Term.app `coe_fn_add [`f `f']) ")") "." `mono)
      [(Term.fun "fun" (Term.basicFun [`x `hx] [] "=>" (Term.hole "_")))])
     ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `integral_congr_ae
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Mathlib.Tactic.tacticSimp_rw__
       "simp_rw"
       (Tactic.rwRuleSeq
        "["
        [(Tactic.rwRule [] `inner_def)
         ","
         (Tactic.rwRule
          [(patternIgnore (token.«← » "←"))]
          (Term.app
           `integral_add
           [(Term.app `integrable_inner [`f `g]) (Term.app `integrable_inner [`f' `g])]))
         ","
         (Tactic.rwRule [(patternIgnore (token.«← » "←"))] `inner_add_left)]
        "]")
       [])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `inner_add_left
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       `integral_add
       [(Term.app `integrable_inner [`f `g]) (Term.app `integrable_inner [`f' `g])])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `integrable_inner [`f' `g])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `g
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `f'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `integrable_inner
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.app `integrable_inner [`f' `g])
     ")")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.app `integrable_inner [`f `g])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `g
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `f
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `integrable_inner
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023,
     term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.app `integrable_inner [`f `g])
     ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `integral_add
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `inner_def
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, tactic) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
      («term_=_»
       (MeasureTheory.L2Cat.MeasureTheory.Function.L2Space.«term⟪_,_⟫»
        "⟪"
        («term_+_» `f "+" `f')
        ", "
        `g
        "⟫")
       "="
       («term_+_» (Term.app `inner [`f `g]) "+" (Term.app `inner [`f' `g])))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_+_» (Term.app `inner [`f `g]) "+" (Term.app `inner [`f' `g]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `inner [`f' `g])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `g
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `f'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `inner
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 66 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 65, term))
      (Term.app `inner [`f `g])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `g
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `f
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `inner
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 65 >? 1022, (some 1023, term) <=? (some 65, term)
[PrettyPrinter.parenthesize] ...precedences are 51 >? 65, (some 66, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 50, term))
      (MeasureTheory.L2Cat.MeasureTheory.Function.L2Space.«term⟪_,_⟫»
       "⟪"
       («term_+_» `f "+" `f')
       ", "
       `g
       "⟫")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'MeasureTheory.L2Cat.MeasureTheory.Function.L2Space.«term⟪_,_⟫»', expected 'MeasureTheory.L2Cat.MeasureTheory.Function.L2Space.term⟪_,_⟫._@.MeasureTheory.Function.L2Space._hyg.10'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.opaque'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.instance'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.axiom'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.example'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.inductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.classInductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.structure'-/-- failed to format: format: uncaught backtrack exception
private
  theorem
    add_left'
    ( f f' g : α →₂[ μ ] E ) : ⟪ f + f' , g ⟫ = inner f g + inner f' g
    :=
      by
        simp_rw
            [
              inner_def
                ,
                ← integral_add integrable_inner f g integrable_inner f' g
                ,
                ← inner_add_left
              ]
          refine' integral_congr_ae coe_fn_add f f' . mono fun x hx => _
          congr
          rwa [ Pi.add_apply ] at hx
#align measure_theory.L2.add_left' measure_theory.L2.add_left'

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers [] [] [(Command.private "private")] [] [] [])
     (Command.theorem
      "theorem"
      (Command.declId `smul_left' [])
      (Command.declSig
       [(Term.explicitBinder
         "("
         [`f `g]
         [":" (MeasureTheory.MeasureTheory.Function.LpSpace.measure_theory.L2 `α " →₂[" `μ "] " `E)]
         []
         ")")
        (Term.explicitBinder "(" [`r] [":" `𝕜] [] ")")]
       (Term.typeSpec
        ":"
        («term_=_»
         (MeasureTheory.L2Cat.MeasureTheory.Function.L2Space.«term⟪_,_⟫»
          "⟪"
          (Algebra.Group.Defs.«term_•_» `r " • " `f)
          ", "
          `g
          "⟫")
         "="
         («term_*_»
          (Term.app (ComplexConjugate.Algebra.Star.Basic.star_ring_end "conj") [`r])
          "*"
          (Term.app `inner [`f `g])))))
      (Command.declValSimple
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
             [(Tactic.rwRule [] `inner_def)
              ","
              (Tactic.rwRule [] `inner_def)
              ","
              (Tactic.rwRule [(patternIgnore (token.«← » "←"))] `smul_eq_mul)
              ","
              (Tactic.rwRule [(patternIgnore (token.«← » "←"))] `integral_smul)]
             "]")
            [])
           []
           (Tactic.refine'
            "refine'"
            (Term.app
             `integral_congr_ae
             [(Term.app
               (Term.proj (Term.app `coe_fn_smul [`r `f]) "." `mono)
               [(Term.fun "fun" (Term.basicFun [`x `hx] [] "=>" (Term.hole "_")))])]))
           []
           (Tactic.rwSeq
            "rw"
            []
            (Tactic.rwRuleSeq
             "["
             [(Tactic.rwRule [] `smul_eq_mul)
              ","
              (Tactic.rwRule [(patternIgnore (token.«← » "←"))] `inner_smul_left)]
             "]")
            [])
           []
           (Tactic.congr "congr" [])
           []
           (Std.Tactic.tacticRwa__
            "rwa"
            (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `Pi.smul_apply)] "]")
            [(Tactic.location "at" (Tactic.locationHyp [`hx] []))])])))
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
           (Tactic.rwRuleSeq
            "["
            [(Tactic.rwRule [] `inner_def)
             ","
             (Tactic.rwRule [] `inner_def)
             ","
             (Tactic.rwRule [(patternIgnore (token.«← » "←"))] `smul_eq_mul)
             ","
             (Tactic.rwRule [(patternIgnore (token.«← » "←"))] `integral_smul)]
            "]")
           [])
          []
          (Tactic.refine'
           "refine'"
           (Term.app
            `integral_congr_ae
            [(Term.app
              (Term.proj (Term.app `coe_fn_smul [`r `f]) "." `mono)
              [(Term.fun "fun" (Term.basicFun [`x `hx] [] "=>" (Term.hole "_")))])]))
          []
          (Tactic.rwSeq
           "rw"
           []
           (Tactic.rwRuleSeq
            "["
            [(Tactic.rwRule [] `smul_eq_mul)
             ","
             (Tactic.rwRule [(patternIgnore (token.«← » "←"))] `inner_smul_left)]
            "]")
           [])
          []
          (Tactic.congr "congr" [])
          []
          (Std.Tactic.tacticRwa__
           "rwa"
           (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `Pi.smul_apply)] "]")
           [(Tactic.location "at" (Tactic.locationHyp [`hx] []))])])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Std.Tactic.tacticRwa__
       "rwa"
       (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `Pi.smul_apply)] "]")
       [(Tactic.location "at" (Tactic.locationHyp [`hx] []))])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.locationHyp', expected 'Lean.Parser.Tactic.locationWildcard'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `hx
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `Pi.smul_apply
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.congr "congr" [])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.rwSeq
       "rw"
       []
       (Tactic.rwRuleSeq
        "["
        [(Tactic.rwRule [] `smul_eq_mul)
         ","
         (Tactic.rwRule [(patternIgnore (token.«← » "←"))] `inner_smul_left)]
        "]")
       [])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `inner_smul_left
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `smul_eq_mul
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.refine'
       "refine'"
       (Term.app
        `integral_congr_ae
        [(Term.app
          (Term.proj (Term.app `coe_fn_smul [`r `f]) "." `mono)
          [(Term.fun "fun" (Term.basicFun [`x `hx] [] "=>" (Term.hole "_")))])]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       `integral_congr_ae
       [(Term.app
         (Term.proj (Term.app `coe_fn_smul [`r `f]) "." `mono)
         [(Term.fun "fun" (Term.basicFun [`x `hx] [] "=>" (Term.hole "_")))])])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       (Term.proj (Term.app `coe_fn_smul [`r `f]) "." `mono)
       [(Term.fun "fun" (Term.basicFun [`x `hx] [] "=>" (Term.hole "_")))])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.fun "fun" (Term.basicFun [`x `hx] [] "=>" (Term.hole "_")))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
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
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (Term.proj (Term.app `coe_fn_smul [`r `f]) "." `mono)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.app `coe_fn_smul [`r `f])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `f
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `r
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `coe_fn_smul
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren "(" (Term.app `coe_fn_smul [`r `f]) ")")
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.app
      (Term.proj (Term.paren "(" (Term.app `coe_fn_smul [`r `f]) ")") "." `mono)
      [(Term.fun "fun" (Term.basicFun [`x `hx] [] "=>" (Term.hole "_")))])
     ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `integral_congr_ae
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
        [(Tactic.rwRule [] `inner_def)
         ","
         (Tactic.rwRule [] `inner_def)
         ","
         (Tactic.rwRule [(patternIgnore (token.«← » "←"))] `smul_eq_mul)
         ","
         (Tactic.rwRule [(patternIgnore (token.«← » "←"))] `integral_smul)]
        "]")
       [])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `integral_smul
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `smul_eq_mul
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `inner_def
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `inner_def
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, tactic) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
      («term_=_»
       (MeasureTheory.L2Cat.MeasureTheory.Function.L2Space.«term⟪_,_⟫»
        "⟪"
        (Algebra.Group.Defs.«term_•_» `r " • " `f)
        ", "
        `g
        "⟫")
       "="
       («term_*_»
        (Term.app (ComplexConjugate.Algebra.Star.Basic.star_ring_end "conj") [`r])
        "*"
        (Term.app `inner [`f `g])))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_*_»
       (Term.app (ComplexConjugate.Algebra.Star.Basic.star_ring_end "conj") [`r])
       "*"
       (Term.app `inner [`f `g]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `inner [`f `g])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `g
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `f
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `inner
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 71 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 70, term))
      (Term.app (ComplexConjugate.Algebra.Star.Basic.star_ring_end "conj") [`r])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `r
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (ComplexConjugate.Algebra.Star.Basic.star_ring_end "conj")
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 70 >? 1022, (some 1023, term) <=? (some 70, term)
[PrettyPrinter.parenthesize] ...precedences are 51 >? 70, (some 71, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 50, term))
      (MeasureTheory.L2Cat.MeasureTheory.Function.L2Space.«term⟪_,_⟫»
       "⟪"
       (Algebra.Group.Defs.«term_•_» `r " • " `f)
       ", "
       `g
       "⟫")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'MeasureTheory.L2Cat.MeasureTheory.Function.L2Space.«term⟪_,_⟫»', expected 'MeasureTheory.L2Cat.MeasureTheory.Function.L2Space.term⟪_,_⟫._@.MeasureTheory.Function.L2Space._hyg.10'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.opaque'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.instance'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.axiom'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.example'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.inductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.classInductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.structure'-/-- failed to format: format: uncaught backtrack exception
private
  theorem
    smul_left'
    ( f g : α →₂[ μ ] E ) ( r : 𝕜 ) : ⟪ r • f , g ⟫ = conj r * inner f g
    :=
      by
        rw [ inner_def , inner_def , ← smul_eq_mul , ← integral_smul ]
          refine' integral_congr_ae coe_fn_smul r f . mono fun x hx => _
          rw [ smul_eq_mul , ← inner_smul_left ]
          congr
          rwa [ Pi.smul_apply ] at hx
#align measure_theory.L2.smul_left' measure_theory.L2.smul_left'

instance innerProductSpace : InnerProductSpace 𝕜 (α →₂[μ] E)
    where
  norm_sq_eq_inner := norm_sq_eq_inner'
  conj_sym _ _ := by simp_rw [inner_def, ← integral_conj, inner_conj_sym]
  add_left := add_left'
  smul_left := smul_left'
#align measure_theory.L2.inner_product_space MeasureTheory.L2Cat.innerProductSpace

end InnerProductSpace

section IndicatorConstLp

variable (𝕜) {s : Set α}

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers
      [(Command.docComment
        "/--"
        "The inner product in `L2` of the indicator of a set `indicator_const_Lp 2 hs hμs c` and `f` is\nequal to the integral of the inner product over `s`: `∫ x in s, ⟪c, f x⟫ ∂μ`. -/")]
      []
      []
      []
      []
      [])
     (Command.theorem
      "theorem"
      (Command.declId `inner_indicator_const_Lp_eq_set_integral_inner [])
      (Command.declSig
       [(Term.explicitBinder "(" [`f] [":" (Term.app `lp [`E (num "2") `μ])] [] ")")
        (Term.explicitBinder "(" [`hs] [":" (Term.app `MeasurableSet [`s])] [] ")")
        (Term.explicitBinder "(" [`c] [":" `E] [] ")")
        (Term.explicitBinder
         "("
         [`hμs]
         [":" («term_≠_» (Term.app `μ [`s]) "≠" (Ennreal.Data.Real.Ennreal.ennreal.top "∞"))]
         []
         ")")]
       (Term.typeSpec
        ":"
        («term_=_»
         (Term.typeAscription
          "("
          (MeasureTheory.L2Cat.MeasureTheory.Function.L2Space.«term⟪_,_⟫»
           "⟪"
           (Term.app `indicatorConstLp [(num "2") `hs `hμs `c])
           ", "
           `f
           "⟫")
          ":"
          [`𝕜]
          ")")
         "="
         (MeasureTheory.MeasureTheory.Integral.Bochner.«term∫_in_,_∂_»
          "∫"
          (Std.ExtendedBinder.extBinders (Std.ExtendedBinder.extBinder (Lean.binderIdent `x) []))
          " in "
          `s
          ", "
          (MeasureTheory.L2Cat.MeasureTheory.Function.L2Space.«term⟪_,_⟫»
           "⟪"
           `c
           ", "
           (Term.app `f [`x])
           "⟫")
          " ∂"
          `μ))))
      (Command.declValSimple
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
             [(Tactic.rwRule [] `inner_def)
              ","
              (Tactic.rwRule
               [(patternIgnore (token.«← » "←"))]
               (Term.app
                `integral_add_compl
                [`hs (Term.app `L2.integrable_inner [(Term.hole "_") `f])]))]
             "]")
            [])
           []
           (Tactic.tacticHave_
            "have"
            (Term.haveDecl
             (Term.haveIdDecl
              [`h_left []]
              [(Term.typeSpec
                ":"
                («term_=_»
                 (MeasureTheory.MeasureTheory.Integral.Bochner.«term∫_in_,_∂_»
                  "∫"
                  (Std.ExtendedBinder.extBinders
                   (Std.ExtendedBinder.extBinder (Lean.binderIdent `x) []))
                  " in "
                  `s
                  ", "
                  (MeasureTheory.L2Cat.MeasureTheory.Function.L2Space.«term⟪_,_⟫»
                   "⟪"
                   (Term.app (Term.app `indicator_const_Lp [(num "2") `hs `hμs `c]) [`x])
                   ", "
                   (Term.app `f [`x])
                   "⟫")
                  " ∂"
                  `μ)
                 "="
                 (MeasureTheory.MeasureTheory.Integral.Bochner.«term∫_in_,_∂_»
                  "∫"
                  (Std.ExtendedBinder.extBinders
                   (Std.ExtendedBinder.extBinder (Lean.binderIdent `x) []))
                  " in "
                  `s
                  ", "
                  (MeasureTheory.L2Cat.MeasureTheory.Function.L2Space.«term⟪_,_⟫»
                   "⟪"
                   `c
                   ", "
                   (Term.app `f [`x])
                   "⟫")
                  " ∂"
                  `μ)))]
              ":="
              (Term.byTactic
               "by"
               (Tactic.tacticSeq
                (Tactic.tacticSeq1Indented
                 [(Mathlib.Tactic.tacticSuffices_
                   "suffices"
                   [`h_ae_eq []]
                   [(Term.typeSpec
                     ":"
                     (MeasureTheory.MeasureTheory.Measure.MeasureSpaceDef.«term∀ᵐ_∂_,_»
                      "∀ᵐ"
                      (Std.ExtendedBinder.extBinders
                       (Std.ExtendedBinder.extBinder (Lean.binderIdent `x) []))
                      " ∂"
                      `μ
                      ", "
                      (Term.arrow
                       («term_∈_» `x "∈" `s)
                       "→"
                       («term_=_»
                        (MeasureTheory.L2Cat.MeasureTheory.Function.L2Space.«term⟪_,_⟫»
                         "⟪"
                         (Term.app `indicator_const_Lp [(num "2") `hs `hμs `c `x])
                         ", "
                         (Term.app `f [`x])
                         "⟫")
                        "="
                        (MeasureTheory.L2Cat.MeasureTheory.Function.L2Space.«term⟪_,_⟫»
                         "⟪"
                         `c
                         ", "
                         (Term.app `f [`x])
                         "⟫")))))])
                  []
                  (Tactic.exact "exact" (Term.app `set_integral_congr_ae [`hs `h_ae_eq]))
                  []
                  (Tactic.tacticHave_
                   "have"
                   (Term.haveDecl
                    (Term.haveIdDecl
                     [`h_indicator []]
                     [(Term.typeSpec
                       ":"
                       (MeasureTheory.MeasureTheory.Measure.MeasureSpaceDef.«term∀ᵐ_∂_,_»
                        "∀ᵐ"
                        (Std.ExtendedBinder.extBinders
                         (Std.ExtendedBinder.extBinder (Lean.binderIdent `x) [(group ":" `α)]))
                        " ∂"
                        `μ
                        ", "
                        (Term.arrow
                         («term_∈_» `x "∈" `s)
                         "→"
                         («term_=_»
                          (Term.app `indicator_const_Lp [(num "2") `hs `hμs `c `x])
                          "="
                          `c))))]
                     ":="
                     `indicator_const_Lp_coe_fn_mem)))
                  []
                  (Tactic.refine'
                   "refine'"
                   (Term.app
                    `h_indicator.mono
                    [(Term.fun "fun" (Term.basicFun [`x `hx `hxs] [] "=>" (Term.hole "_")))]))
                  []
                  (Tactic.congr "congr" [])
                  []
                  (Tactic.exact "exact" (Term.app `hx [`hxs]))]))))))
           []
           (Tactic.tacticHave_
            "have"
            (Term.haveDecl
             (Term.haveIdDecl
              [`h_right []]
              [(Term.typeSpec
                ":"
                («term_=_»
                 (MeasureTheory.MeasureTheory.Integral.Bochner.«term∫_in_,_∂_»
                  "∫"
                  (Std.ExtendedBinder.extBinders
                   (Std.ExtendedBinder.extBinder (Lean.binderIdent `x) []))
                  " in "
                  (Order.Basic.«term_ᶜ» `s "ᶜ")
                  ", "
                  (MeasureTheory.L2Cat.MeasureTheory.Function.L2Space.«term⟪_,_⟫»
                   "⟪"
                   (Term.app (Term.app `indicator_const_Lp [(num "2") `hs `hμs `c]) [`x])
                   ", "
                   (Term.app `f [`x])
                   "⟫")
                  " ∂"
                  `μ)
                 "="
                 (num "0")))]
              ":="
              (Term.byTactic
               "by"
               (Tactic.tacticSeq
                (Tactic.tacticSeq1Indented
                 [(Mathlib.Tactic.tacticSuffices_
                   "suffices"
                   [`h_ae_eq []]
                   [(Term.typeSpec
                     ":"
                     (MeasureTheory.MeasureTheory.Measure.MeasureSpaceDef.«term∀ᵐ_∂_,_»
                      "∀ᵐ"
                      (Std.ExtendedBinder.extBinders
                       (Std.ExtendedBinder.extBinder (Lean.binderIdent `x) []))
                      " ∂"
                      `μ
                      ", "
                      (Term.arrow
                       («term_∉_» `x "∉" `s)
                       "→"
                       («term_=_»
                        (MeasureTheory.L2Cat.MeasureTheory.Function.L2Space.«term⟪_,_⟫»
                         "⟪"
                         (Term.app `indicator_const_Lp [(num "2") `hs `hμs `c `x])
                         ", "
                         (Term.app `f [`x])
                         "⟫")
                        "="
                        (num "0")))))])
                  []
                  (tactic__
                   (cdotTk (patternIgnore (token.«· » "·")))
                   [(Mathlib.Tactic.tacticSimp_rw__
                     "simp_rw"
                     (Tactic.rwRuleSeq
                      "["
                      [(Tactic.rwRule [(patternIgnore (token.«← » "←"))] `Set.mem_compl_iff)]
                      "]")
                     [(Tactic.location "at" (Tactic.locationHyp [`h_ae_eq] []))])
                    []
                    (Mathlib.Tactic.tacticSuffices_
                     "suffices"
                     [`h_int_zero []]
                     [(Term.typeSpec
                       ":"
                       («term_=_»
                        (MeasureTheory.MeasureTheory.Integral.Bochner.«term∫_in_,_∂_»
                         "∫"
                         (Std.ExtendedBinder.extBinders
                          (Std.ExtendedBinder.extBinder (Lean.binderIdent `x) []))
                         " in "
                         (Order.Basic.«term_ᶜ» `s "ᶜ")
                         ", "
                         (Term.app
                          `inner
                          [(Term.app `indicator_const_Lp [(num "2") `hs `hμs `c `x])
                           (Term.app `f [`x])])
                         " ∂"
                         `μ)
                        "="
                        (MeasureTheory.MeasureTheory.Integral.Bochner.«term∫_in_,_∂_»
                         "∫"
                         (Std.ExtendedBinder.extBinders
                          (Std.ExtendedBinder.extBinder (Lean.binderIdent `x) []))
                         " in "
                         (Order.Basic.«term_ᶜ» `s "ᶜ")
                         ", "
                         (Term.typeAscription "(" (num "0") ":" [`𝕜] ")")
                         " ∂"
                         `μ)))])
                    []
                    (tactic__
                     (cdotTk (patternIgnore (token.«· » "·")))
                     [(Tactic.rwSeq
                       "rw"
                       []
                       (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `h_int_zero)] "]")
                       [])
                      []
                      (Tactic.simp "simp" [] [] [] [] [])])
                    []
                    (Tactic.exact "exact" (Term.app `set_integral_congr_ae [`hs.compl `h_ae_eq]))])
                  []
                  (Tactic.tacticHave_
                   "have"
                   (Term.haveDecl
                    (Term.haveIdDecl
                     [`h_indicator []]
                     [(Term.typeSpec
                       ":"
                       (MeasureTheory.MeasureTheory.Measure.MeasureSpaceDef.«term∀ᵐ_∂_,_»
                        "∀ᵐ"
                        (Std.ExtendedBinder.extBinders
                         (Std.ExtendedBinder.extBinder (Lean.binderIdent `x) [(group ":" `α)]))
                        " ∂"
                        `μ
                        ", "
                        (Term.arrow
                         («term_∉_» `x "∉" `s)
                         "→"
                         («term_=_»
                          (Term.app `indicator_const_Lp [(num "2") `hs `hμs `c `x])
                          "="
                          (num "0")))))]
                     ":="
                     `indicator_const_Lp_coe_fn_nmem)))
                  []
                  (Tactic.refine'
                   "refine'"
                   (Term.app
                    `h_indicator.mono
                    [(Term.fun "fun" (Term.basicFun [`x `hx `hxs] [] "=>" (Term.hole "_")))]))
                  []
                  (Tactic.rwSeq
                   "rw"
                   []
                   (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] (Term.app `hx [`hxs]))] "]")
                   [])
                  []
                  (Tactic.exact "exact" `inner_zero_left)]))))))
           []
           (Tactic.rwSeq
            "rw"
            []
            (Tactic.rwRuleSeq
             "["
             [(Tactic.rwRule [] `h_left)
              ","
              (Tactic.rwRule [] `h_right)
              ","
              (Tactic.rwRule [] `add_zero)]
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
         [(Tactic.rwSeq
           "rw"
           []
           (Tactic.rwRuleSeq
            "["
            [(Tactic.rwRule [] `inner_def)
             ","
             (Tactic.rwRule
              [(patternIgnore (token.«← » "←"))]
              (Term.app
               `integral_add_compl
               [`hs (Term.app `L2.integrable_inner [(Term.hole "_") `f])]))]
            "]")
           [])
          []
          (Tactic.tacticHave_
           "have"
           (Term.haveDecl
            (Term.haveIdDecl
             [`h_left []]
             [(Term.typeSpec
               ":"
               («term_=_»
                (MeasureTheory.MeasureTheory.Integral.Bochner.«term∫_in_,_∂_»
                 "∫"
                 (Std.ExtendedBinder.extBinders
                  (Std.ExtendedBinder.extBinder (Lean.binderIdent `x) []))
                 " in "
                 `s
                 ", "
                 (MeasureTheory.L2Cat.MeasureTheory.Function.L2Space.«term⟪_,_⟫»
                  "⟪"
                  (Term.app (Term.app `indicator_const_Lp [(num "2") `hs `hμs `c]) [`x])
                  ", "
                  (Term.app `f [`x])
                  "⟫")
                 " ∂"
                 `μ)
                "="
                (MeasureTheory.MeasureTheory.Integral.Bochner.«term∫_in_,_∂_»
                 "∫"
                 (Std.ExtendedBinder.extBinders
                  (Std.ExtendedBinder.extBinder (Lean.binderIdent `x) []))
                 " in "
                 `s
                 ", "
                 (MeasureTheory.L2Cat.MeasureTheory.Function.L2Space.«term⟪_,_⟫»
                  "⟪"
                  `c
                  ", "
                  (Term.app `f [`x])
                  "⟫")
                 " ∂"
                 `μ)))]
             ":="
             (Term.byTactic
              "by"
              (Tactic.tacticSeq
               (Tactic.tacticSeq1Indented
                [(Mathlib.Tactic.tacticSuffices_
                  "suffices"
                  [`h_ae_eq []]
                  [(Term.typeSpec
                    ":"
                    (MeasureTheory.MeasureTheory.Measure.MeasureSpaceDef.«term∀ᵐ_∂_,_»
                     "∀ᵐ"
                     (Std.ExtendedBinder.extBinders
                      (Std.ExtendedBinder.extBinder (Lean.binderIdent `x) []))
                     " ∂"
                     `μ
                     ", "
                     (Term.arrow
                      («term_∈_» `x "∈" `s)
                      "→"
                      («term_=_»
                       (MeasureTheory.L2Cat.MeasureTheory.Function.L2Space.«term⟪_,_⟫»
                        "⟪"
                        (Term.app `indicator_const_Lp [(num "2") `hs `hμs `c `x])
                        ", "
                        (Term.app `f [`x])
                        "⟫")
                       "="
                       (MeasureTheory.L2Cat.MeasureTheory.Function.L2Space.«term⟪_,_⟫»
                        "⟪"
                        `c
                        ", "
                        (Term.app `f [`x])
                        "⟫")))))])
                 []
                 (Tactic.exact "exact" (Term.app `set_integral_congr_ae [`hs `h_ae_eq]))
                 []
                 (Tactic.tacticHave_
                  "have"
                  (Term.haveDecl
                   (Term.haveIdDecl
                    [`h_indicator []]
                    [(Term.typeSpec
                      ":"
                      (MeasureTheory.MeasureTheory.Measure.MeasureSpaceDef.«term∀ᵐ_∂_,_»
                       "∀ᵐ"
                       (Std.ExtendedBinder.extBinders
                        (Std.ExtendedBinder.extBinder (Lean.binderIdent `x) [(group ":" `α)]))
                       " ∂"
                       `μ
                       ", "
                       (Term.arrow
                        («term_∈_» `x "∈" `s)
                        "→"
                        («term_=_»
                         (Term.app `indicator_const_Lp [(num "2") `hs `hμs `c `x])
                         "="
                         `c))))]
                    ":="
                    `indicator_const_Lp_coe_fn_mem)))
                 []
                 (Tactic.refine'
                  "refine'"
                  (Term.app
                   `h_indicator.mono
                   [(Term.fun "fun" (Term.basicFun [`x `hx `hxs] [] "=>" (Term.hole "_")))]))
                 []
                 (Tactic.congr "congr" [])
                 []
                 (Tactic.exact "exact" (Term.app `hx [`hxs]))]))))))
          []
          (Tactic.tacticHave_
           "have"
           (Term.haveDecl
            (Term.haveIdDecl
             [`h_right []]
             [(Term.typeSpec
               ":"
               («term_=_»
                (MeasureTheory.MeasureTheory.Integral.Bochner.«term∫_in_,_∂_»
                 "∫"
                 (Std.ExtendedBinder.extBinders
                  (Std.ExtendedBinder.extBinder (Lean.binderIdent `x) []))
                 " in "
                 (Order.Basic.«term_ᶜ» `s "ᶜ")
                 ", "
                 (MeasureTheory.L2Cat.MeasureTheory.Function.L2Space.«term⟪_,_⟫»
                  "⟪"
                  (Term.app (Term.app `indicator_const_Lp [(num "2") `hs `hμs `c]) [`x])
                  ", "
                  (Term.app `f [`x])
                  "⟫")
                 " ∂"
                 `μ)
                "="
                (num "0")))]
             ":="
             (Term.byTactic
              "by"
              (Tactic.tacticSeq
               (Tactic.tacticSeq1Indented
                [(Mathlib.Tactic.tacticSuffices_
                  "suffices"
                  [`h_ae_eq []]
                  [(Term.typeSpec
                    ":"
                    (MeasureTheory.MeasureTheory.Measure.MeasureSpaceDef.«term∀ᵐ_∂_,_»
                     "∀ᵐ"
                     (Std.ExtendedBinder.extBinders
                      (Std.ExtendedBinder.extBinder (Lean.binderIdent `x) []))
                     " ∂"
                     `μ
                     ", "
                     (Term.arrow
                      («term_∉_» `x "∉" `s)
                      "→"
                      («term_=_»
                       (MeasureTheory.L2Cat.MeasureTheory.Function.L2Space.«term⟪_,_⟫»
                        "⟪"
                        (Term.app `indicator_const_Lp [(num "2") `hs `hμs `c `x])
                        ", "
                        (Term.app `f [`x])
                        "⟫")
                       "="
                       (num "0")))))])
                 []
                 (tactic__
                  (cdotTk (patternIgnore (token.«· » "·")))
                  [(Mathlib.Tactic.tacticSimp_rw__
                    "simp_rw"
                    (Tactic.rwRuleSeq
                     "["
                     [(Tactic.rwRule [(patternIgnore (token.«← » "←"))] `Set.mem_compl_iff)]
                     "]")
                    [(Tactic.location "at" (Tactic.locationHyp [`h_ae_eq] []))])
                   []
                   (Mathlib.Tactic.tacticSuffices_
                    "suffices"
                    [`h_int_zero []]
                    [(Term.typeSpec
                      ":"
                      («term_=_»
                       (MeasureTheory.MeasureTheory.Integral.Bochner.«term∫_in_,_∂_»
                        "∫"
                        (Std.ExtendedBinder.extBinders
                         (Std.ExtendedBinder.extBinder (Lean.binderIdent `x) []))
                        " in "
                        (Order.Basic.«term_ᶜ» `s "ᶜ")
                        ", "
                        (Term.app
                         `inner
                         [(Term.app `indicator_const_Lp [(num "2") `hs `hμs `c `x])
                          (Term.app `f [`x])])
                        " ∂"
                        `μ)
                       "="
                       (MeasureTheory.MeasureTheory.Integral.Bochner.«term∫_in_,_∂_»
                        "∫"
                        (Std.ExtendedBinder.extBinders
                         (Std.ExtendedBinder.extBinder (Lean.binderIdent `x) []))
                        " in "
                        (Order.Basic.«term_ᶜ» `s "ᶜ")
                        ", "
                        (Term.typeAscription "(" (num "0") ":" [`𝕜] ")")
                        " ∂"
                        `μ)))])
                   []
                   (tactic__
                    (cdotTk (patternIgnore (token.«· » "·")))
                    [(Tactic.rwSeq
                      "rw"
                      []
                      (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `h_int_zero)] "]")
                      [])
                     []
                     (Tactic.simp "simp" [] [] [] [] [])])
                   []
                   (Tactic.exact "exact" (Term.app `set_integral_congr_ae [`hs.compl `h_ae_eq]))])
                 []
                 (Tactic.tacticHave_
                  "have"
                  (Term.haveDecl
                   (Term.haveIdDecl
                    [`h_indicator []]
                    [(Term.typeSpec
                      ":"
                      (MeasureTheory.MeasureTheory.Measure.MeasureSpaceDef.«term∀ᵐ_∂_,_»
                       "∀ᵐ"
                       (Std.ExtendedBinder.extBinders
                        (Std.ExtendedBinder.extBinder (Lean.binderIdent `x) [(group ":" `α)]))
                       " ∂"
                       `μ
                       ", "
                       (Term.arrow
                        («term_∉_» `x "∉" `s)
                        "→"
                        («term_=_»
                         (Term.app `indicator_const_Lp [(num "2") `hs `hμs `c `x])
                         "="
                         (num "0")))))]
                    ":="
                    `indicator_const_Lp_coe_fn_nmem)))
                 []
                 (Tactic.refine'
                  "refine'"
                  (Term.app
                   `h_indicator.mono
                   [(Term.fun "fun" (Term.basicFun [`x `hx `hxs] [] "=>" (Term.hole "_")))]))
                 []
                 (Tactic.rwSeq
                  "rw"
                  []
                  (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] (Term.app `hx [`hxs]))] "]")
                  [])
                 []
                 (Tactic.exact "exact" `inner_zero_left)]))))))
          []
          (Tactic.rwSeq
           "rw"
           []
           (Tactic.rwRuleSeq
            "["
            [(Tactic.rwRule [] `h_left)
             ","
             (Tactic.rwRule [] `h_right)
             ","
             (Tactic.rwRule [] `add_zero)]
            "]")
           [])])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.rwSeq
       "rw"
       []
       (Tactic.rwRuleSeq
        "["
        [(Tactic.rwRule [] `h_left)
         ","
         (Tactic.rwRule [] `h_right)
         ","
         (Tactic.rwRule [] `add_zero)]
        "]")
       [])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `add_zero
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `h_right
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `h_left
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.tacticHave_
       "have"
       (Term.haveDecl
        (Term.haveIdDecl
         [`h_right []]
         [(Term.typeSpec
           ":"
           («term_=_»
            (MeasureTheory.MeasureTheory.Integral.Bochner.«term∫_in_,_∂_»
             "∫"
             (Std.ExtendedBinder.extBinders (Std.ExtendedBinder.extBinder (Lean.binderIdent `x) []))
             " in "
             (Order.Basic.«term_ᶜ» `s "ᶜ")
             ", "
             (MeasureTheory.L2Cat.MeasureTheory.Function.L2Space.«term⟪_,_⟫»
              "⟪"
              (Term.app (Term.app `indicator_const_Lp [(num "2") `hs `hμs `c]) [`x])
              ", "
              (Term.app `f [`x])
              "⟫")
             " ∂"
             `μ)
            "="
            (num "0")))]
         ":="
         (Term.byTactic
          "by"
          (Tactic.tacticSeq
           (Tactic.tacticSeq1Indented
            [(Mathlib.Tactic.tacticSuffices_
              "suffices"
              [`h_ae_eq []]
              [(Term.typeSpec
                ":"
                (MeasureTheory.MeasureTheory.Measure.MeasureSpaceDef.«term∀ᵐ_∂_,_»
                 "∀ᵐ"
                 (Std.ExtendedBinder.extBinders
                  (Std.ExtendedBinder.extBinder (Lean.binderIdent `x) []))
                 " ∂"
                 `μ
                 ", "
                 (Term.arrow
                  («term_∉_» `x "∉" `s)
                  "→"
                  («term_=_»
                   (MeasureTheory.L2Cat.MeasureTheory.Function.L2Space.«term⟪_,_⟫»
                    "⟪"
                    (Term.app `indicator_const_Lp [(num "2") `hs `hμs `c `x])
                    ", "
                    (Term.app `f [`x])
                    "⟫")
                   "="
                   (num "0")))))])
             []
             (tactic__
              (cdotTk (patternIgnore (token.«· » "·")))
              [(Mathlib.Tactic.tacticSimp_rw__
                "simp_rw"
                (Tactic.rwRuleSeq
                 "["
                 [(Tactic.rwRule [(patternIgnore (token.«← » "←"))] `Set.mem_compl_iff)]
                 "]")
                [(Tactic.location "at" (Tactic.locationHyp [`h_ae_eq] []))])
               []
               (Mathlib.Tactic.tacticSuffices_
                "suffices"
                [`h_int_zero []]
                [(Term.typeSpec
                  ":"
                  («term_=_»
                   (MeasureTheory.MeasureTheory.Integral.Bochner.«term∫_in_,_∂_»
                    "∫"
                    (Std.ExtendedBinder.extBinders
                     (Std.ExtendedBinder.extBinder (Lean.binderIdent `x) []))
                    " in "
                    (Order.Basic.«term_ᶜ» `s "ᶜ")
                    ", "
                    (Term.app
                     `inner
                     [(Term.app `indicator_const_Lp [(num "2") `hs `hμs `c `x]) (Term.app `f [`x])])
                    " ∂"
                    `μ)
                   "="
                   (MeasureTheory.MeasureTheory.Integral.Bochner.«term∫_in_,_∂_»
                    "∫"
                    (Std.ExtendedBinder.extBinders
                     (Std.ExtendedBinder.extBinder (Lean.binderIdent `x) []))
                    " in "
                    (Order.Basic.«term_ᶜ» `s "ᶜ")
                    ", "
                    (Term.typeAscription "(" (num "0") ":" [`𝕜] ")")
                    " ∂"
                    `μ)))])
               []
               (tactic__
                (cdotTk (patternIgnore (token.«· » "·")))
                [(Tactic.rwSeq
                  "rw"
                  []
                  (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `h_int_zero)] "]")
                  [])
                 []
                 (Tactic.simp "simp" [] [] [] [] [])])
               []
               (Tactic.exact "exact" (Term.app `set_integral_congr_ae [`hs.compl `h_ae_eq]))])
             []
             (Tactic.tacticHave_
              "have"
              (Term.haveDecl
               (Term.haveIdDecl
                [`h_indicator []]
                [(Term.typeSpec
                  ":"
                  (MeasureTheory.MeasureTheory.Measure.MeasureSpaceDef.«term∀ᵐ_∂_,_»
                   "∀ᵐ"
                   (Std.ExtendedBinder.extBinders
                    (Std.ExtendedBinder.extBinder (Lean.binderIdent `x) [(group ":" `α)]))
                   " ∂"
                   `μ
                   ", "
                   (Term.arrow
                    («term_∉_» `x "∉" `s)
                    "→"
                    («term_=_»
                     (Term.app `indicator_const_Lp [(num "2") `hs `hμs `c `x])
                     "="
                     (num "0")))))]
                ":="
                `indicator_const_Lp_coe_fn_nmem)))
             []
             (Tactic.refine'
              "refine'"
              (Term.app
               `h_indicator.mono
               [(Term.fun "fun" (Term.basicFun [`x `hx `hxs] [] "=>" (Term.hole "_")))]))
             []
             (Tactic.rwSeq
              "rw"
              []
              (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] (Term.app `hx [`hxs]))] "]")
              [])
             []
             (Tactic.exact "exact" `inner_zero_left)]))))))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.byTactic
       "by"
       (Tactic.tacticSeq
        (Tactic.tacticSeq1Indented
         [(Mathlib.Tactic.tacticSuffices_
           "suffices"
           [`h_ae_eq []]
           [(Term.typeSpec
             ":"
             (MeasureTheory.MeasureTheory.Measure.MeasureSpaceDef.«term∀ᵐ_∂_,_»
              "∀ᵐ"
              (Std.ExtendedBinder.extBinders
               (Std.ExtendedBinder.extBinder (Lean.binderIdent `x) []))
              " ∂"
              `μ
              ", "
              (Term.arrow
               («term_∉_» `x "∉" `s)
               "→"
               («term_=_»
                (MeasureTheory.L2Cat.MeasureTheory.Function.L2Space.«term⟪_,_⟫»
                 "⟪"
                 (Term.app `indicator_const_Lp [(num "2") `hs `hμs `c `x])
                 ", "
                 (Term.app `f [`x])
                 "⟫")
                "="
                (num "0")))))])
          []
          (tactic__
           (cdotTk (patternIgnore (token.«· » "·")))
           [(Mathlib.Tactic.tacticSimp_rw__
             "simp_rw"
             (Tactic.rwRuleSeq
              "["
              [(Tactic.rwRule [(patternIgnore (token.«← » "←"))] `Set.mem_compl_iff)]
              "]")
             [(Tactic.location "at" (Tactic.locationHyp [`h_ae_eq] []))])
            []
            (Mathlib.Tactic.tacticSuffices_
             "suffices"
             [`h_int_zero []]
             [(Term.typeSpec
               ":"
               («term_=_»
                (MeasureTheory.MeasureTheory.Integral.Bochner.«term∫_in_,_∂_»
                 "∫"
                 (Std.ExtendedBinder.extBinders
                  (Std.ExtendedBinder.extBinder (Lean.binderIdent `x) []))
                 " in "
                 (Order.Basic.«term_ᶜ» `s "ᶜ")
                 ", "
                 (Term.app
                  `inner
                  [(Term.app `indicator_const_Lp [(num "2") `hs `hμs `c `x]) (Term.app `f [`x])])
                 " ∂"
                 `μ)
                "="
                (MeasureTheory.MeasureTheory.Integral.Bochner.«term∫_in_,_∂_»
                 "∫"
                 (Std.ExtendedBinder.extBinders
                  (Std.ExtendedBinder.extBinder (Lean.binderIdent `x) []))
                 " in "
                 (Order.Basic.«term_ᶜ» `s "ᶜ")
                 ", "
                 (Term.typeAscription "(" (num "0") ":" [`𝕜] ")")
                 " ∂"
                 `μ)))])
            []
            (tactic__
             (cdotTk (patternIgnore (token.«· » "·")))
             [(Tactic.rwSeq "rw" [] (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `h_int_zero)] "]") [])
              []
              (Tactic.simp "simp" [] [] [] [] [])])
            []
            (Tactic.exact "exact" (Term.app `set_integral_congr_ae [`hs.compl `h_ae_eq]))])
          []
          (Tactic.tacticHave_
           "have"
           (Term.haveDecl
            (Term.haveIdDecl
             [`h_indicator []]
             [(Term.typeSpec
               ":"
               (MeasureTheory.MeasureTheory.Measure.MeasureSpaceDef.«term∀ᵐ_∂_,_»
                "∀ᵐ"
                (Std.ExtendedBinder.extBinders
                 (Std.ExtendedBinder.extBinder (Lean.binderIdent `x) [(group ":" `α)]))
                " ∂"
                `μ
                ", "
                (Term.arrow
                 («term_∉_» `x "∉" `s)
                 "→"
                 («term_=_»
                  (Term.app `indicator_const_Lp [(num "2") `hs `hμs `c `x])
                  "="
                  (num "0")))))]
             ":="
             `indicator_const_Lp_coe_fn_nmem)))
          []
          (Tactic.refine'
           "refine'"
           (Term.app
            `h_indicator.mono
            [(Term.fun "fun" (Term.basicFun [`x `hx `hxs] [] "=>" (Term.hole "_")))]))
          []
          (Tactic.rwSeq
           "rw"
           []
           (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] (Term.app `hx [`hxs]))] "]")
           [])
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
      (Tactic.rwSeq
       "rw"
       []
       (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] (Term.app `hx [`hxs]))] "]")
       [])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `hx [`hxs])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `hxs
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `hx
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.refine'
       "refine'"
       (Term.app
        `h_indicator.mono
        [(Term.fun "fun" (Term.basicFun [`x `hx `hxs] [] "=>" (Term.hole "_")))]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       `h_indicator.mono
       [(Term.fun "fun" (Term.basicFun [`x `hx `hxs] [] "=>" (Term.hole "_")))])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.fun "fun" (Term.basicFun [`x `hx `hxs] [] "=>" (Term.hole "_")))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.strictImplicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.implicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.instBinder'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `hxs
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.strictImplicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.implicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.instBinder'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `hx
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.strictImplicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.implicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.instBinder'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `x
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `h_indicator.mono
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.tacticHave_
       "have"
       (Term.haveDecl
        (Term.haveIdDecl
         [`h_indicator []]
         [(Term.typeSpec
           ":"
           (MeasureTheory.MeasureTheory.Measure.MeasureSpaceDef.«term∀ᵐ_∂_,_»
            "∀ᵐ"
            (Std.ExtendedBinder.extBinders
             (Std.ExtendedBinder.extBinder (Lean.binderIdent `x) [(group ":" `α)]))
            " ∂"
            `μ
            ", "
            (Term.arrow
             («term_∉_» `x "∉" `s)
             "→"
             («term_=_» (Term.app `indicator_const_Lp [(num "2") `hs `hμs `c `x]) "=" (num "0")))))]
         ":="
         `indicator_const_Lp_coe_fn_nmem)))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `indicator_const_Lp_coe_fn_nmem
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (MeasureTheory.MeasureTheory.Measure.MeasureSpaceDef.«term∀ᵐ_∂_,_»
       "∀ᵐ"
       (Std.ExtendedBinder.extBinders
        (Std.ExtendedBinder.extBinder (Lean.binderIdent `x) [(group ":" `α)]))
       " ∂"
       `μ
       ", "
       (Term.arrow
        («term_∉_» `x "∉" `s)
        "→"
        («term_=_» (Term.app `indicator_const_Lp [(num "2") `hs `hμs `c `x]) "=" (num "0"))))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.arrow
       («term_∉_» `x "∉" `s)
       "→"
       («term_=_» (Term.app `indicator_const_Lp [(num "2") `hs `hμs `c `x]) "=" (num "0")))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_=_» (Term.app `indicator_const_Lp [(num "2") `hs `hμs `c `x]) "=" (num "0"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (num "0")
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 50, term))
      (Term.app `indicator_const_Lp [(num "2") `hs `hμs `c `x])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `x
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `c
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `hμs
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `hs
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'num', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'num', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (num "2")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `indicator_const_Lp
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1022, (some 1023, term) <=? (some 50, term)
[PrettyPrinter.parenthesize] ...precedences are 25 >? 50, (some 51, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 25, term))
      («term_∉_» `x "∉" `s)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `s
[PrettyPrinter.parenthesize] ...precedences are 50 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 50, term))
      `x
[PrettyPrinter.parenthesize] ...precedences are 50 >? 1024, (none, [anonymous]) <=? (some 50, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 50, (some 50, term) <=? (some 25, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 25, (some 25, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `μ
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `α
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (tactic__
       (cdotTk (patternIgnore (token.«· » "·")))
       [(Mathlib.Tactic.tacticSimp_rw__
         "simp_rw"
         (Tactic.rwRuleSeq
          "["
          [(Tactic.rwRule [(patternIgnore (token.«← » "←"))] `Set.mem_compl_iff)]
          "]")
         [(Tactic.location "at" (Tactic.locationHyp [`h_ae_eq] []))])
        []
        (Mathlib.Tactic.tacticSuffices_
         "suffices"
         [`h_int_zero []]
         [(Term.typeSpec
           ":"
           («term_=_»
            (MeasureTheory.MeasureTheory.Integral.Bochner.«term∫_in_,_∂_»
             "∫"
             (Std.ExtendedBinder.extBinders (Std.ExtendedBinder.extBinder (Lean.binderIdent `x) []))
             " in "
             (Order.Basic.«term_ᶜ» `s "ᶜ")
             ", "
             (Term.app
              `inner
              [(Term.app `indicator_const_Lp [(num "2") `hs `hμs `c `x]) (Term.app `f [`x])])
             " ∂"
             `μ)
            "="
            (MeasureTheory.MeasureTheory.Integral.Bochner.«term∫_in_,_∂_»
             "∫"
             (Std.ExtendedBinder.extBinders (Std.ExtendedBinder.extBinder (Lean.binderIdent `x) []))
             " in "
             (Order.Basic.«term_ᶜ» `s "ᶜ")
             ", "
             (Term.typeAscription "(" (num "0") ":" [`𝕜] ")")
             " ∂"
             `μ)))])
        []
        (tactic__
         (cdotTk (patternIgnore (token.«· » "·")))
         [(Tactic.rwSeq "rw" [] (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `h_int_zero)] "]") [])
          []
          (Tactic.simp "simp" [] [] [] [] [])])
        []
        (Tactic.exact "exact" (Term.app `set_integral_congr_ae [`hs.compl `h_ae_eq]))])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.exact "exact" (Term.app `set_integral_congr_ae [`hs.compl `h_ae_eq]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `set_integral_congr_ae [`hs.compl `h_ae_eq])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `h_ae_eq
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `hs.compl
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `set_integral_congr_ae
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (tactic__
       (cdotTk (patternIgnore (token.«· » "·")))
       [(Tactic.rwSeq "rw" [] (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `h_int_zero)] "]") [])
        []
        (Tactic.simp "simp" [] [] [] [] [])])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.simp "simp" [] [] [] [] [])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.rwSeq "rw" [] (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `h_int_zero)] "]") [])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `h_int_zero
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Mathlib.Tactic.tacticSuffices_
       "suffices"
       [`h_int_zero []]
       [(Term.typeSpec
         ":"
         («term_=_»
          (MeasureTheory.MeasureTheory.Integral.Bochner.«term∫_in_,_∂_»
           "∫"
           (Std.ExtendedBinder.extBinders (Std.ExtendedBinder.extBinder (Lean.binderIdent `x) []))
           " in "
           (Order.Basic.«term_ᶜ» `s "ᶜ")
           ", "
           (Term.app
            `inner
            [(Term.app `indicator_const_Lp [(num "2") `hs `hμs `c `x]) (Term.app `f [`x])])
           " ∂"
           `μ)
          "="
          (MeasureTheory.MeasureTheory.Integral.Bochner.«term∫_in_,_∂_»
           "∫"
           (Std.ExtendedBinder.extBinders (Std.ExtendedBinder.extBinder (Lean.binderIdent `x) []))
           " in "
           (Order.Basic.«term_ᶜ» `s "ᶜ")
           ", "
           (Term.typeAscription "(" (num "0") ":" [`𝕜] ")")
           " ∂"
           `μ)))])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_=_»
       (MeasureTheory.MeasureTheory.Integral.Bochner.«term∫_in_,_∂_»
        "∫"
        (Std.ExtendedBinder.extBinders (Std.ExtendedBinder.extBinder (Lean.binderIdent `x) []))
        " in "
        (Order.Basic.«term_ᶜ» `s "ᶜ")
        ", "
        (Term.app
         `inner
         [(Term.app `indicator_const_Lp [(num "2") `hs `hμs `c `x]) (Term.app `f [`x])])
        " ∂"
        `μ)
       "="
       (MeasureTheory.MeasureTheory.Integral.Bochner.«term∫_in_,_∂_»
        "∫"
        (Std.ExtendedBinder.extBinders (Std.ExtendedBinder.extBinder (Lean.binderIdent `x) []))
        " in "
        (Order.Basic.«term_ᶜ» `s "ᶜ")
        ", "
        (Term.typeAscription "(" (num "0") ":" [`𝕜] ")")
        " ∂"
        `μ))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (MeasureTheory.MeasureTheory.Integral.Bochner.«term∫_in_,_∂_»
       "∫"
       (Std.ExtendedBinder.extBinders (Std.ExtendedBinder.extBinder (Lean.binderIdent `x) []))
       " in "
       (Order.Basic.«term_ᶜ» `s "ᶜ")
       ", "
       (Term.typeAscription "(" (num "0") ":" [`𝕜] ")")
       " ∂"
       `μ)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `μ
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.typeAscription "(" (num "0") ":" [`𝕜] ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `𝕜
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (num "0")
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Order.Basic.«term_ᶜ» `s "ᶜ")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 999, term))
      `s
[PrettyPrinter.parenthesize] ...precedences are 999 >? 1024, (none,
     [anonymous]) <=? (some 999, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 999, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1022, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 50, term))
      (MeasureTheory.MeasureTheory.Integral.Bochner.«term∫_in_,_∂_»
       "∫"
       (Std.ExtendedBinder.extBinders (Std.ExtendedBinder.extBinder (Lean.binderIdent `x) []))
       " in "
       (Order.Basic.«term_ᶜ» `s "ᶜ")
       ", "
       (Term.app
        `inner
        [(Term.app `indicator_const_Lp [(num "2") `hs `hμs `c `x]) (Term.app `f [`x])])
       " ∂"
       `μ)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `μ
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       `inner
       [(Term.app `indicator_const_Lp [(num "2") `hs `hμs `c `x]) (Term.app `f [`x])])
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
      (Term.app `indicator_const_Lp [(num "2") `hs `hμs `c `x])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `x
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `c
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `hμs
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `hs
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'num', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'num', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (num "2")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `indicator_const_Lp
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023,
     term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.app `indicator_const_Lp [(num "2") `hs `hμs `c `x])
     ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `inner
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Order.Basic.«term_ᶜ» `s "ᶜ")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 999, term))
      `s
[PrettyPrinter.parenthesize] ...precedences are 999 >? 1024, (none,
     [anonymous]) <=? (some 999, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 999, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1022, (some 0, term) <=? (some 50, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (MeasureTheory.MeasureTheory.Integral.Bochner.«term∫_in_,_∂_»
      "∫"
      (Std.ExtendedBinder.extBinders (Std.ExtendedBinder.extBinder (Lean.binderIdent `x) []))
      " in "
      (Order.Basic.«term_ᶜ» `s "ᶜ")
      ", "
      (Term.app
       `inner
       [(Term.paren "(" (Term.app `indicator_const_Lp [(num "2") `hs `hμs `c `x]) ")")
        (Term.paren "(" (Term.app `f [`x]) ")")])
      " ∂"
      `μ)
     ")")
[PrettyPrinter.parenthesize] ...precedences are 0 >? 50, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Mathlib.Tactic.tacticSimp_rw__
       "simp_rw"
       (Tactic.rwRuleSeq
        "["
        [(Tactic.rwRule [(patternIgnore (token.«← » "←"))] `Set.mem_compl_iff)]
        "]")
       [(Tactic.location "at" (Tactic.locationHyp [`h_ae_eq] []))])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.locationHyp', expected 'Lean.Parser.Tactic.locationWildcard'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `h_ae_eq
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `Set.mem_compl_iff
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Mathlib.Tactic.tacticSuffices_
       "suffices"
       [`h_ae_eq []]
       [(Term.typeSpec
         ":"
         (MeasureTheory.MeasureTheory.Measure.MeasureSpaceDef.«term∀ᵐ_∂_,_»
          "∀ᵐ"
          (Std.ExtendedBinder.extBinders (Std.ExtendedBinder.extBinder (Lean.binderIdent `x) []))
          " ∂"
          `μ
          ", "
          (Term.arrow
           («term_∉_» `x "∉" `s)
           "→"
           («term_=_»
            (MeasureTheory.L2Cat.MeasureTheory.Function.L2Space.«term⟪_,_⟫»
             "⟪"
             (Term.app `indicator_const_Lp [(num "2") `hs `hμs `c `x])
             ", "
             (Term.app `f [`x])
             "⟫")
            "="
            (num "0")))))])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (MeasureTheory.MeasureTheory.Measure.MeasureSpaceDef.«term∀ᵐ_∂_,_»
       "∀ᵐ"
       (Std.ExtendedBinder.extBinders (Std.ExtendedBinder.extBinder (Lean.binderIdent `x) []))
       " ∂"
       `μ
       ", "
       (Term.arrow
        («term_∉_» `x "∉" `s)
        "→"
        («term_=_»
         (MeasureTheory.L2Cat.MeasureTheory.Function.L2Space.«term⟪_,_⟫»
          "⟪"
          (Term.app `indicator_const_Lp [(num "2") `hs `hμs `c `x])
          ", "
          (Term.app `f [`x])
          "⟫")
         "="
         (num "0"))))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.arrow
       («term_∉_» `x "∉" `s)
       "→"
       («term_=_»
        (MeasureTheory.L2Cat.MeasureTheory.Function.L2Space.«term⟪_,_⟫»
         "⟪"
         (Term.app `indicator_const_Lp [(num "2") `hs `hμs `c `x])
         ", "
         (Term.app `f [`x])
         "⟫")
        "="
        (num "0")))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_=_»
       (MeasureTheory.L2Cat.MeasureTheory.Function.L2Space.«term⟪_,_⟫»
        "⟪"
        (Term.app `indicator_const_Lp [(num "2") `hs `hμs `c `x])
        ", "
        (Term.app `f [`x])
        "⟫")
       "="
       (num "0"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (num "0")
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 50, term))
      (MeasureTheory.L2Cat.MeasureTheory.Function.L2Space.«term⟪_,_⟫»
       "⟪"
       (Term.app `indicator_const_Lp [(num "2") `hs `hμs `c `x])
       ", "
       (Term.app `f [`x])
       "⟫")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'MeasureTheory.L2Cat.MeasureTheory.Function.L2Space.«term⟪_,_⟫»', expected 'MeasureTheory.L2Cat.MeasureTheory.Function.L2Space.term⟪_,_⟫._@.MeasureTheory.Function.L2Space._hyg.10'
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
/--
    The inner product in `L2` of the indicator of a set `indicator_const_Lp 2 hs hμs c` and `f` is
    equal to the integral of the inner product over `s`: `∫ x in s, ⟪c, f x⟫ ∂μ`. -/
  theorem
    inner_indicator_const_Lp_eq_set_integral_inner
    ( f : lp E 2 μ ) ( hs : MeasurableSet s ) ( c : E ) ( hμs : μ s ≠ ∞ )
      : ( ⟪ indicatorConstLp 2 hs hμs c , f ⟫ : 𝕜 ) = ∫ x in s , ⟪ c , f x ⟫ ∂ μ
    :=
      by
        rw [ inner_def , ← integral_add_compl hs L2.integrable_inner _ f ]
          have
            h_left
              :
                ∫ x in s , ⟪ indicator_const_Lp 2 hs hμs c x , f x ⟫ ∂ μ
                  =
                  ∫ x in s , ⟪ c , f x ⟫ ∂ μ
              :=
              by
                suffices
                    h_ae_eq
                    : ∀ᵐ x ∂ μ , x ∈ s → ⟪ indicator_const_Lp 2 hs hμs c x , f x ⟫ = ⟪ c , f x ⟫
                  exact set_integral_congr_ae hs h_ae_eq
                  have
                    h_indicator
                      : ∀ᵐ x : α ∂ μ , x ∈ s → indicator_const_Lp 2 hs hμs c x = c
                      :=
                      indicator_const_Lp_coe_fn_mem
                  refine' h_indicator.mono fun x hx hxs => _
                  congr
                  exact hx hxs
          have
            h_right
              : ∫ x in s ᶜ , ⟪ indicator_const_Lp 2 hs hμs c x , f x ⟫ ∂ μ = 0
              :=
              by
                suffices h_ae_eq : ∀ᵐ x ∂ μ , x ∉ s → ⟪ indicator_const_Lp 2 hs hμs c x , f x ⟫ = 0
                  ·
                    simp_rw [ ← Set.mem_compl_iff ] at h_ae_eq
                      suffices
                        h_int_zero
                        :
                          ∫ x in s ᶜ , inner indicator_const_Lp 2 hs hμs c x f x ∂ μ
                            =
                            ∫ x in s ᶜ , ( 0 : 𝕜 ) ∂ μ
                      · rw [ h_int_zero ] simp
                      exact set_integral_congr_ae hs.compl h_ae_eq
                  have
                    h_indicator
                      : ∀ᵐ x : α ∂ μ , x ∉ s → indicator_const_Lp 2 hs hμs c x = 0
                      :=
                      indicator_const_Lp_coe_fn_nmem
                  refine' h_indicator.mono fun x hx hxs => _
                  rw [ hx hxs ]
                  exact inner_zero_left
          rw [ h_left , h_right , add_zero ]
#align
  measure_theory.L2.inner_indicator_const_Lp_eq_set_integral_inner MeasureTheory.L2Cat.inner_indicator_const_Lp_eq_set_integral_inner

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers
      [(Command.docComment
        "/--"
        "The inner product in `L2` of the indicator of a set `indicator_const_Lp 2 hs hμs c` and `f` is\nequal to the inner product of the constant `c` and the integral of `f` over `s`. -/")]
      []
      []
      []
      []
      [])
     (Command.theorem
      "theorem"
      (Command.declId `inner_indicator_const_Lp_eq_inner_set_integral [])
      (Command.declSig
       [(Term.instBinder "[" [] (Term.app `CompleteSpace [`E]) "]")
        (Term.instBinder "[" [] (Term.app `NormedSpace [(Data.Real.Basic.termℝ "ℝ") `E]) "]")
        (Term.explicitBinder "(" [`hs] [":" (Term.app `MeasurableSet [`s])] [] ")")
        (Term.explicitBinder
         "("
         [`hμs]
         [":" («term_≠_» (Term.app `μ [`s]) "≠" (Ennreal.Data.Real.Ennreal.ennreal.top "∞"))]
         []
         ")")
        (Term.explicitBinder "(" [`c] [":" `E] [] ")")
        (Term.explicitBinder "(" [`f] [":" (Term.app `lp [`E (num "2") `μ])] [] ")")]
       (Term.typeSpec
        ":"
        («term_=_»
         (Term.typeAscription
          "("
          (MeasureTheory.L2Cat.MeasureTheory.Function.L2Space.«term⟪_,_⟫»
           "⟪"
           (Term.app `indicatorConstLp [(num "2") `hs `hμs `c])
           ", "
           `f
           "⟫")
          ":"
          [`𝕜]
          ")")
         "="
         (MeasureTheory.L2Cat.MeasureTheory.Function.L2Space.«term⟪_,_⟫»
          "⟪"
          `c
          ", "
          (MeasureTheory.MeasureTheory.Integral.Bochner.«term∫_in_,_∂_»
           "∫"
           (Std.ExtendedBinder.extBinders (Std.ExtendedBinder.extBinder (Lean.binderIdent `x) []))
           " in "
           `s
           ", "
           (Term.app `f [`x])
           " ∂"
           `μ)
          "⟫"))))
      (Command.declValSimple
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
                `integral_inner
                [(Term.app
                  `integrable_on_Lp_of_measure_ne_top
                  [`f `fact_one_le_two_ennreal.elim `hμs])]))
              ","
              (Tactic.rwRule [] `L2.inner_indicator_const_Lp_eq_set_integral_inner)]
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
         [(Tactic.rwSeq
           "rw"
           []
           (Tactic.rwRuleSeq
            "["
            [(Tactic.rwRule
              [(patternIgnore (token.«← » "←"))]
              (Term.app
               `integral_inner
               [(Term.app
                 `integrable_on_Lp_of_measure_ne_top
                 [`f `fact_one_le_two_ennreal.elim `hμs])]))
             ","
             (Tactic.rwRule [] `L2.inner_indicator_const_Lp_eq_set_integral_inner)]
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
          [(patternIgnore (token.«← » "←"))]
          (Term.app
           `integral_inner
           [(Term.app
             `integrable_on_Lp_of_measure_ne_top
             [`f `fact_one_le_two_ennreal.elim `hμs])]))
         ","
         (Tactic.rwRule [] `L2.inner_indicator_const_Lp_eq_set_integral_inner)]
        "]")
       [])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `L2.inner_indicator_const_Lp_eq_set_integral_inner
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       `integral_inner
       [(Term.app `integrable_on_Lp_of_measure_ne_top [`f `fact_one_le_two_ennreal.elim `hμs])])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `integrable_on_Lp_of_measure_ne_top [`f `fact_one_le_two_ennreal.elim `hμs])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `hμs
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `fact_one_le_two_ennreal.elim
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `f
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `integrable_on_Lp_of_measure_ne_top
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.app `integrable_on_Lp_of_measure_ne_top [`f `fact_one_le_two_ennreal.elim `hμs])
     ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `integral_inner
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, tactic) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
      («term_=_»
       (Term.typeAscription
        "("
        (MeasureTheory.L2Cat.MeasureTheory.Function.L2Space.«term⟪_,_⟫»
         "⟪"
         (Term.app `indicatorConstLp [(num "2") `hs `hμs `c])
         ", "
         `f
         "⟫")
        ":"
        [`𝕜]
        ")")
       "="
       (MeasureTheory.L2Cat.MeasureTheory.Function.L2Space.«term⟪_,_⟫»
        "⟪"
        `c
        ", "
        (MeasureTheory.MeasureTheory.Integral.Bochner.«term∫_in_,_∂_»
         "∫"
         (Std.ExtendedBinder.extBinders (Std.ExtendedBinder.extBinder (Lean.binderIdent `x) []))
         " in "
         `s
         ", "
         (Term.app `f [`x])
         " ∂"
         `μ)
        "⟫"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (MeasureTheory.L2Cat.MeasureTheory.Function.L2Space.«term⟪_,_⟫»
       "⟪"
       `c
       ", "
       (MeasureTheory.MeasureTheory.Integral.Bochner.«term∫_in_,_∂_»
        "∫"
        (Std.ExtendedBinder.extBinders (Std.ExtendedBinder.extBinder (Lean.binderIdent `x) []))
        " in "
        `s
        ", "
        (Term.app `f [`x])
        " ∂"
        `μ)
       "⟫")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'MeasureTheory.L2Cat.MeasureTheory.Function.L2Space.«term⟪_,_⟫»', expected 'MeasureTheory.L2Cat.MeasureTheory.Function.L2Space.term⟪_,_⟫._@.MeasureTheory.Function.L2Space._hyg.10'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.opaque'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.instance'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.axiom'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.example'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.inductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.classInductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.structure'-/-- failed to format: format: uncaught backtrack exception
/--
    The inner product in `L2` of the indicator of a set `indicator_const_Lp 2 hs hμs c` and `f` is
    equal to the inner product of the constant `c` and the integral of `f` over `s`. -/
  theorem
    inner_indicator_const_Lp_eq_inner_set_integral
    [ CompleteSpace E ]
        [ NormedSpace ℝ E ]
        ( hs : MeasurableSet s )
        ( hμs : μ s ≠ ∞ )
        ( c : E )
        ( f : lp E 2 μ )
      : ( ⟪ indicatorConstLp 2 hs hμs c , f ⟫ : 𝕜 ) = ⟪ c , ∫ x in s , f x ∂ μ ⟫
    :=
      by
        rw
          [
            ← integral_inner integrable_on_Lp_of_measure_ne_top f fact_one_le_two_ennreal.elim hμs
              ,
              L2.inner_indicator_const_Lp_eq_set_integral_inner
            ]
#align
  measure_theory.L2.inner_indicator_const_Lp_eq_inner_set_integral MeasureTheory.L2Cat.inner_indicator_const_Lp_eq_inner_set_integral

variable {𝕜}

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers
      [(Command.docComment
        "/--"
        "The inner product in `L2` of the indicator of a set `indicator_const_Lp 2 hs hμs (1 : 𝕜)` and\na real or complex function `f` is equal to the integral of `f` over `s`. -/")]
      []
      []
      []
      []
      [])
     (Command.theorem
      "theorem"
      (Command.declId `inner_indicator_const_Lp_one [])
      (Command.declSig
       [(Term.explicitBinder "(" [`hs] [":" (Term.app `MeasurableSet [`s])] [] ")")
        (Term.explicitBinder
         "("
         [`hμs]
         [":" («term_≠_» (Term.app `μ [`s]) "≠" (Ennreal.Data.Real.Ennreal.ennreal.top "∞"))]
         []
         ")")
        (Term.explicitBinder "(" [`f] [":" (Term.app `lp [`𝕜 (num "2") `μ])] [] ")")]
       (Term.typeSpec
        ":"
        («term_=_»
         (MeasureTheory.L2Cat.MeasureTheory.Function.L2Space.«term⟪_,_⟫»
          "⟪"
          (Term.app
           `indicatorConstLp
           [(num "2") `hs `hμs (Term.typeAscription "(" (num "1") ":" [`𝕜] ")")])
          ", "
          `f
          "⟫")
         "="
         (MeasureTheory.MeasureTheory.Integral.Bochner.«term∫_in_,_∂_»
          "∫"
          (Std.ExtendedBinder.extBinders (Std.ExtendedBinder.extBinder (Lean.binderIdent `x) []))
          " in "
          `s
          ", "
          (Term.app `f [`x])
          " ∂"
          `μ))))
      (Command.declValSimple
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
               []
               (Term.app
                `L2.inner_indicator_const_Lp_eq_inner_set_integral
                [`𝕜 `hs `hμs (Term.typeAscription "(" (num "1") ":" [`𝕜] ")") `f]))]
             "]")
            [])
           []
           (Tactic.simp "simp" [] [] [] [] [])])))
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
           (Tactic.rwRuleSeq
            "["
            [(Tactic.rwRule
              []
              (Term.app
               `L2.inner_indicator_const_Lp_eq_inner_set_integral
               [`𝕜 `hs `hμs (Term.typeAscription "(" (num "1") ":" [`𝕜] ")") `f]))]
            "]")
           [])
          []
          (Tactic.simp "simp" [] [] [] [] [])])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.simp "simp" [] [] [] [] [])
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
           `L2.inner_indicator_const_Lp_eq_inner_set_integral
           [`𝕜 `hs `hμs (Term.typeAscription "(" (num "1") ":" [`𝕜] ")") `f]))]
        "]")
       [])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       `L2.inner_indicator_const_Lp_eq_inner_set_integral
       [`𝕜 `hs `hμs (Term.typeAscription "(" (num "1") ":" [`𝕜] ")") `f])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `f
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.typeAscription', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.typeAscription', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.typeAscription "(" (num "1") ":" [`𝕜] ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `𝕜
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (num "1")
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, term))
      `hμs
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1023, term)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `hs
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `𝕜
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `L2.inner_indicator_const_Lp_eq_inner_set_integral
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, tactic) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
      («term_=_»
       (MeasureTheory.L2Cat.MeasureTheory.Function.L2Space.«term⟪_,_⟫»
        "⟪"
        (Term.app
         `indicatorConstLp
         [(num "2") `hs `hμs (Term.typeAscription "(" (num "1") ":" [`𝕜] ")")])
        ", "
        `f
        "⟫")
       "="
       (MeasureTheory.MeasureTheory.Integral.Bochner.«term∫_in_,_∂_»
        "∫"
        (Std.ExtendedBinder.extBinders (Std.ExtendedBinder.extBinder (Lean.binderIdent `x) []))
        " in "
        `s
        ", "
        (Term.app `f [`x])
        " ∂"
        `μ))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (MeasureTheory.MeasureTheory.Integral.Bochner.«term∫_in_,_∂_»
       "∫"
       (Std.ExtendedBinder.extBinders (Std.ExtendedBinder.extBinder (Lean.binderIdent `x) []))
       " in "
       `s
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
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `s
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1022, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 50, term))
      (MeasureTheory.L2Cat.MeasureTheory.Function.L2Space.«term⟪_,_⟫»
       "⟪"
       (Term.app
        `indicatorConstLp
        [(num "2") `hs `hμs (Term.typeAscription "(" (num "1") ":" [`𝕜] ")")])
       ", "
       `f
       "⟫")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'MeasureTheory.L2Cat.MeasureTheory.Function.L2Space.«term⟪_,_⟫»', expected 'MeasureTheory.L2Cat.MeasureTheory.Function.L2Space.term⟪_,_⟫._@.MeasureTheory.Function.L2Space._hyg.10'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.opaque'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.instance'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.axiom'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.example'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.inductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.classInductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.structure'-/-- failed to format: format: uncaught backtrack exception
/--
    The inner product in `L2` of the indicator of a set `indicator_const_Lp 2 hs hμs (1 : 𝕜)` and
    a real or complex function `f` is equal to the integral of `f` over `s`. -/
  theorem
    inner_indicator_const_Lp_one
    ( hs : MeasurableSet s ) ( hμs : μ s ≠ ∞ ) ( f : lp 𝕜 2 μ )
      : ⟪ indicatorConstLp 2 hs hμs ( 1 : 𝕜 ) , f ⟫ = ∫ x in s , f x ∂ μ
    := by rw [ L2.inner_indicator_const_Lp_eq_inner_set_integral 𝕜 hs hμs ( 1 : 𝕜 ) f ] simp
#align
  measure_theory.L2.inner_indicator_const_Lp_one MeasureTheory.L2Cat.inner_indicator_const_Lp_one

end IndicatorConstLp

end L2Cat

section InnerContinuous

variable {α : Type _} [TopologicalSpace α] [MeasureSpace α] [BorelSpace α] {𝕜 : Type _} [IsROrC 𝕜]

variable (μ : Measure α) [IsFiniteMeasure μ]

open BoundedContinuousFunction ComplexConjugate

-- mathport name: «expr⟪ , ⟫»
local notation "⟪" x ", " y "⟫" => @inner 𝕜 (α →₂[μ] 𝕜) _ x y

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers
      [(Command.docComment
        "/--"
        "For bounded continuous functions `f`, `g` on a finite-measure topological space `α`, the L^2\ninner product is the integral of their pointwise inner product. -/")]
      []
      []
      []
      []
      [])
     (Command.theorem
      "theorem"
      (Command.declId `BoundedContinuousFunction.inner_to_Lp [])
      (Command.declSig
       [(Term.explicitBinder
         "("
         [`f `g]
         [":"
          (BoundedContinuousFunction.Topology.ContinuousFunction.Bounded.bounded_continuous_function
           `α
           " →ᵇ "
           `𝕜)]
         []
         ")")]
       (Term.typeSpec
        ":"
        («term_=_»
         (MeasureTheory.MeasureTheory.Function.L2Space.«term⟪_,_⟫»
          "⟪"
          (Term.app `BoundedContinuousFunction.toLp [(num "2") `μ `𝕜 `f])
          ", "
          (Term.app `BoundedContinuousFunction.toLp [(num "2") `μ `𝕜 `g])
          "⟫")
         "="
         (MeasureTheory.MeasureTheory.Integral.Bochner.«term∫_,_∂_»
          "∫"
          (Std.ExtendedBinder.extBinders (Std.ExtendedBinder.extBinder (Lean.binderIdent `x) []))
          ", "
          («term_*_»
           (Term.app
            (ComplexConjugate.Algebra.Star.Basic.star_ring_end "conj")
            [(Term.app `f [`x])])
           "*"
           (Term.app `g [`x]))
          " ∂"
          `μ))))
      (Command.declValSimple
       ":="
       (Term.byTactic
        "by"
        (Tactic.tacticSeq
         (Tactic.tacticSeq1Indented
          [(Tactic.apply "apply" `integral_congr_ae)
           []
           (Tactic.tacticHave_
            "have"
            (Term.haveDecl (Term.haveIdDecl [`hf_ae []] [] ":=" (Term.app `f.coe_fn_to_Lp [`μ]))))
           []
           (Tactic.tacticHave_
            "have"
            (Term.haveDecl (Term.haveIdDecl [`hg_ae []] [] ":=" (Term.app `g.coe_fn_to_Lp [`μ]))))
           []
           (Tactic.filterUpwards
            "filter_upwards"
            [(Tactic.termList "[" [`hf_ae "," `hg_ae] "]")]
            ["with" [(Term.hole "_") `hf `hg]]
            [])
           []
           (Tactic.rwSeq
            "rw"
            []
            (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `hf) "," (Tactic.rwRule [] `hg)] "]")
            [])
           []
           (Tactic.simp "simp" [] [] [] [] [])])))
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
         [(Tactic.apply "apply" `integral_congr_ae)
          []
          (Tactic.tacticHave_
           "have"
           (Term.haveDecl (Term.haveIdDecl [`hf_ae []] [] ":=" (Term.app `f.coe_fn_to_Lp [`μ]))))
          []
          (Tactic.tacticHave_
           "have"
           (Term.haveDecl (Term.haveIdDecl [`hg_ae []] [] ":=" (Term.app `g.coe_fn_to_Lp [`μ]))))
          []
          (Tactic.filterUpwards
           "filter_upwards"
           [(Tactic.termList "[" [`hf_ae "," `hg_ae] "]")]
           ["with" [(Term.hole "_") `hf `hg]]
           [])
          []
          (Tactic.rwSeq
           "rw"
           []
           (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `hf) "," (Tactic.rwRule [] `hg)] "]")
           [])
          []
          (Tactic.simp "simp" [] [] [] [] [])])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.simp "simp" [] [] [] [] [])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.rwSeq
       "rw"
       []
       (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `hf) "," (Tactic.rwRule [] `hg)] "]")
       [])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `hg
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `hf
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.filterUpwards
       "filter_upwards"
       [(Tactic.termList "[" [`hf_ae "," `hg_ae] "]")]
       ["with" [(Term.hole "_") `hf `hg]]
       [])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `hg
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `hf
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `hg_ae
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `hf_ae
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.tacticHave_
       "have"
       (Term.haveDecl (Term.haveIdDecl [`hg_ae []] [] ":=" (Term.app `g.coe_fn_to_Lp [`μ]))))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `g.coe_fn_to_Lp [`μ])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `μ
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `g.coe_fn_to_Lp
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.tacticHave_
       "have"
       (Term.haveDecl (Term.haveIdDecl [`hf_ae []] [] ":=" (Term.app `f.coe_fn_to_Lp [`μ]))))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `f.coe_fn_to_Lp [`μ])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `μ
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `f.coe_fn_to_Lp
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.apply "apply" `integral_congr_ae)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `integral_congr_ae
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, tactic) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
      («term_=_»
       (MeasureTheory.MeasureTheory.Function.L2Space.«term⟪_,_⟫»
        "⟪"
        (Term.app `BoundedContinuousFunction.toLp [(num "2") `μ `𝕜 `f])
        ", "
        (Term.app `BoundedContinuousFunction.toLp [(num "2") `μ `𝕜 `g])
        "⟫")
       "="
       (MeasureTheory.MeasureTheory.Integral.Bochner.«term∫_,_∂_»
        "∫"
        (Std.ExtendedBinder.extBinders (Std.ExtendedBinder.extBinder (Lean.binderIdent `x) []))
        ", "
        («term_*_»
         (Term.app (ComplexConjugate.Algebra.Star.Basic.star_ring_end "conj") [(Term.app `f [`x])])
         "*"
         (Term.app `g [`x]))
        " ∂"
        `μ))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (MeasureTheory.MeasureTheory.Integral.Bochner.«term∫_,_∂_»
       "∫"
       (Std.ExtendedBinder.extBinders (Std.ExtendedBinder.extBinder (Lean.binderIdent `x) []))
       ", "
       («term_*_»
        (Term.app (ComplexConjugate.Algebra.Star.Basic.star_ring_end "conj") [(Term.app `f [`x])])
        "*"
        (Term.app `g [`x]))
       " ∂"
       `μ)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `μ
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_*_»
       (Term.app (ComplexConjugate.Algebra.Star.Basic.star_ring_end "conj") [(Term.app `f [`x])])
       "*"
       (Term.app `g [`x]))
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
[PrettyPrinter.parenthesize] ...precedences are 71 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 70, term))
      (Term.app (ComplexConjugate.Algebra.Star.Basic.star_ring_end "conj") [(Term.app `f [`x])])
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
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (ComplexConjugate.Algebra.Star.Basic.star_ring_end "conj")
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 70 >? 1022, (some 1023, term) <=? (some 70, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 70, (some 71, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1022, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 50, term))
      (MeasureTheory.MeasureTheory.Function.L2Space.«term⟪_,_⟫»
       "⟪"
       (Term.app `BoundedContinuousFunction.toLp [(num "2") `μ `𝕜 `f])
       ", "
       (Term.app `BoundedContinuousFunction.toLp [(num "2") `μ `𝕜 `g])
       "⟫")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'MeasureTheory.MeasureTheory.Function.L2Space.«term⟪_,_⟫»', expected 'MeasureTheory.MeasureTheory.Function.L2Space.term⟪_,_⟫._@.MeasureTheory.Function.L2Space._hyg.84'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.opaque'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.instance'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.axiom'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.example'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.inductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.classInductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.structure'-/-- failed to format: format: uncaught backtrack exception
/--
    For bounded continuous functions `f`, `g` on a finite-measure topological space `α`, the L^2
    inner product is the integral of their pointwise inner product. -/
  theorem
    BoundedContinuousFunction.inner_to_Lp
    ( f g : α →ᵇ 𝕜 )
      :
        ⟪ BoundedContinuousFunction.toLp 2 μ 𝕜 f , BoundedContinuousFunction.toLp 2 μ 𝕜 g ⟫
          =
          ∫ x , conj f x * g x ∂ μ
    :=
      by
        apply integral_congr_ae
          have hf_ae := f.coe_fn_to_Lp μ
          have hg_ae := g.coe_fn_to_Lp μ
          filter_upwards [ hf_ae , hg_ae ] with _ hf hg
          rw [ hf , hg ]
          simp
#align
  measure_theory.bounded_continuous_function.inner_to_Lp MeasureTheory.BoundedContinuousFunction.inner_to_Lp

variable [CompactSpace α]

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers
      [(Command.docComment
        "/--"
        "For continuous functions `f`, `g` on a compact, finite-measure topological space `α`, the L^2\ninner product is the integral of their pointwise inner product. -/")]
      []
      []
      []
      []
      [])
     (Command.theorem
      "theorem"
      (Command.declId `ContinuousMap.inner_to_Lp [])
      (Command.declSig
       [(Term.explicitBinder
         "("
         [`f `g]
         [":" (Topology.ContinuousFunction.Basic.«termC(_,_)» "C(" `α ", " `𝕜 ")")]
         []
         ")")]
       (Term.typeSpec
        ":"
        («term_=_»
         (MeasureTheory.MeasureTheory.Function.L2Space.«term⟪_,_⟫»
          "⟪"
          (Term.app `ContinuousMap.toLp [(num "2") `μ `𝕜 `f])
          ", "
          (Term.app `ContinuousMap.toLp [(num "2") `μ `𝕜 `g])
          "⟫")
         "="
         (MeasureTheory.MeasureTheory.Integral.Bochner.«term∫_,_∂_»
          "∫"
          (Std.ExtendedBinder.extBinders (Std.ExtendedBinder.extBinder (Lean.binderIdent `x) []))
          ", "
          («term_*_»
           (Term.app
            (ComplexConjugate.Algebra.Star.Basic.star_ring_end "conj")
            [(Term.app `f [`x])])
           "*"
           (Term.app `g [`x]))
          " ∂"
          `μ))))
      (Command.declValSimple
       ":="
       (Term.byTactic
        "by"
        (Tactic.tacticSeq
         (Tactic.tacticSeq1Indented
          [(Tactic.apply "apply" `integral_congr_ae)
           []
           (Tactic.tacticHave_
            "have"
            (Term.haveDecl (Term.haveIdDecl [`hf_ae []] [] ":=" (Term.app `f.coe_fn_to_Lp [`μ]))))
           []
           (Tactic.tacticHave_
            "have"
            (Term.haveDecl (Term.haveIdDecl [`hg_ae []] [] ":=" (Term.app `g.coe_fn_to_Lp [`μ]))))
           []
           (Tactic.filterUpwards
            "filter_upwards"
            [(Tactic.termList "[" [`hf_ae "," `hg_ae] "]")]
            ["with" [(Term.hole "_") `hf `hg]]
            [])
           []
           (Tactic.rwSeq
            "rw"
            []
            (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `hf) "," (Tactic.rwRule [] `hg)] "]")
            [])
           []
           (Tactic.simp "simp" [] [] [] [] [])])))
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
         [(Tactic.apply "apply" `integral_congr_ae)
          []
          (Tactic.tacticHave_
           "have"
           (Term.haveDecl (Term.haveIdDecl [`hf_ae []] [] ":=" (Term.app `f.coe_fn_to_Lp [`μ]))))
          []
          (Tactic.tacticHave_
           "have"
           (Term.haveDecl (Term.haveIdDecl [`hg_ae []] [] ":=" (Term.app `g.coe_fn_to_Lp [`μ]))))
          []
          (Tactic.filterUpwards
           "filter_upwards"
           [(Tactic.termList "[" [`hf_ae "," `hg_ae] "]")]
           ["with" [(Term.hole "_") `hf `hg]]
           [])
          []
          (Tactic.rwSeq
           "rw"
           []
           (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `hf) "," (Tactic.rwRule [] `hg)] "]")
           [])
          []
          (Tactic.simp "simp" [] [] [] [] [])])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.simp "simp" [] [] [] [] [])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.rwSeq
       "rw"
       []
       (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `hf) "," (Tactic.rwRule [] `hg)] "]")
       [])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `hg
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `hf
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.filterUpwards
       "filter_upwards"
       [(Tactic.termList "[" [`hf_ae "," `hg_ae] "]")]
       ["with" [(Term.hole "_") `hf `hg]]
       [])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `hg
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `hf
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `hg_ae
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `hf_ae
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.tacticHave_
       "have"
       (Term.haveDecl (Term.haveIdDecl [`hg_ae []] [] ":=" (Term.app `g.coe_fn_to_Lp [`μ]))))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `g.coe_fn_to_Lp [`μ])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `μ
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `g.coe_fn_to_Lp
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.tacticHave_
       "have"
       (Term.haveDecl (Term.haveIdDecl [`hf_ae []] [] ":=" (Term.app `f.coe_fn_to_Lp [`μ]))))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `f.coe_fn_to_Lp [`μ])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `μ
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `f.coe_fn_to_Lp
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.apply "apply" `integral_congr_ae)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `integral_congr_ae
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, tactic) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
      («term_=_»
       (MeasureTheory.MeasureTheory.Function.L2Space.«term⟪_,_⟫»
        "⟪"
        (Term.app `ContinuousMap.toLp [(num "2") `μ `𝕜 `f])
        ", "
        (Term.app `ContinuousMap.toLp [(num "2") `μ `𝕜 `g])
        "⟫")
       "="
       (MeasureTheory.MeasureTheory.Integral.Bochner.«term∫_,_∂_»
        "∫"
        (Std.ExtendedBinder.extBinders (Std.ExtendedBinder.extBinder (Lean.binderIdent `x) []))
        ", "
        («term_*_»
         (Term.app (ComplexConjugate.Algebra.Star.Basic.star_ring_end "conj") [(Term.app `f [`x])])
         "*"
         (Term.app `g [`x]))
        " ∂"
        `μ))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (MeasureTheory.MeasureTheory.Integral.Bochner.«term∫_,_∂_»
       "∫"
       (Std.ExtendedBinder.extBinders (Std.ExtendedBinder.extBinder (Lean.binderIdent `x) []))
       ", "
       («term_*_»
        (Term.app (ComplexConjugate.Algebra.Star.Basic.star_ring_end "conj") [(Term.app `f [`x])])
        "*"
        (Term.app `g [`x]))
       " ∂"
       `μ)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `μ
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_*_»
       (Term.app (ComplexConjugate.Algebra.Star.Basic.star_ring_end "conj") [(Term.app `f [`x])])
       "*"
       (Term.app `g [`x]))
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
[PrettyPrinter.parenthesize] ...precedences are 71 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 70, term))
      (Term.app (ComplexConjugate.Algebra.Star.Basic.star_ring_end "conj") [(Term.app `f [`x])])
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
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (ComplexConjugate.Algebra.Star.Basic.star_ring_end "conj")
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 70 >? 1022, (some 1023, term) <=? (some 70, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 70, (some 71, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1022, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 50, term))
      (MeasureTheory.MeasureTheory.Function.L2Space.«term⟪_,_⟫»
       "⟪"
       (Term.app `ContinuousMap.toLp [(num "2") `μ `𝕜 `f])
       ", "
       (Term.app `ContinuousMap.toLp [(num "2") `μ `𝕜 `g])
       "⟫")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'MeasureTheory.MeasureTheory.Function.L2Space.«term⟪_,_⟫»', expected 'MeasureTheory.MeasureTheory.Function.L2Space.term⟪_,_⟫._@.MeasureTheory.Function.L2Space._hyg.84'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.opaque'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.instance'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.axiom'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.example'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.inductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.classInductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.structure'-/-- failed to format: format: uncaught backtrack exception
/--
    For continuous functions `f`, `g` on a compact, finite-measure topological space `α`, the L^2
    inner product is the integral of their pointwise inner product. -/
  theorem
    ContinuousMap.inner_to_Lp
    ( f g : C( α , 𝕜 ) )
      : ⟪ ContinuousMap.toLp 2 μ 𝕜 f , ContinuousMap.toLp 2 μ 𝕜 g ⟫ = ∫ x , conj f x * g x ∂ μ
    :=
      by
        apply integral_congr_ae
          have hf_ae := f.coe_fn_to_Lp μ
          have hg_ae := g.coe_fn_to_Lp μ
          filter_upwards [ hf_ae , hg_ae ] with _ hf hg
          rw [ hf , hg ]
          simp
#align measure_theory.continuous_map.inner_to_Lp MeasureTheory.ContinuousMap.inner_to_Lp

end InnerContinuous

end MeasureTheory

