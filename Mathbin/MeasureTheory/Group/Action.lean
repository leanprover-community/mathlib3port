/-
Copyright (c) 2021 Yury G. Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury G. Kudryashov

! This file was ported from Lean 3 source module measure_theory.group.action
! leanprover-community/mathlib commit 7c523cb78f4153682c2929e3006c863bfef463d0
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.MeasureTheory.Group.MeasurableEquiv
import Mathbin.MeasureTheory.Measure.Regular
import Mathbin.Dynamics.Ergodic.MeasurePreserving
import Mathbin.Dynamics.Minimal

/-!
# Measures invariant under group actions

A measure `μ : measure α` is said to be *invariant* under an action of a group `G` if scalar
multiplication by `c : G` is a measure preserving map for all `c`. In this file we define a
typeclass for measures invariant under action of an (additive or multiplicative) group and prove
some basic properties of such measures.
-/


open Ennreal Nnreal Pointwise TopologicalSpace

open MeasureTheory MeasureTheory.Measure Set Function

namespace MeasureTheory

variable {G M α : Type _} {s : Set α}

/- ./././Mathport/Syntax/Translate/Command.lean:379:30: infer kinds are unsupported in Lean 4: #[`measure_preimage_vadd] [] -/
/-- A measure `μ : measure α` is invariant under an additive action of `M` on `α` if for any
measurable set `s : set α` and `c : M`, the measure of its preimage under `λ x, c +ᵥ x` is equal to
the measure of `s`. -/
class VaddInvariantMeasure (M α : Type _) [VAdd M α] {_ : MeasurableSpace α} (μ : Measure α) :
  Prop where
  measure_preimage_vadd : ∀ (c : M) ⦃s : Set α⦄, MeasurableSet s → μ ((fun x => c +ᵥ x) ⁻¹' s) = μ s
#align measure_theory.vadd_invariant_measure MeasureTheory.VaddInvariantMeasure

/- ./././Mathport/Syntax/Translate/Command.lean:379:30: infer kinds are unsupported in Lean 4: #[`measure_preimage_smul] [] -/
/-- A measure `μ : measure α` is invariant under a multiplicative action of `M` on `α` if for any
measurable set `s : set α` and `c : M`, the measure of its preimage under `λ x, c • x` is equal to
the measure of `s`. -/
@[to_additive]
class SmulInvariantMeasure (M α : Type _) [SMul M α] {_ : MeasurableSpace α} (μ : Measure α) :
  Prop where
  measure_preimage_smul : ∀ (c : M) ⦃s : Set α⦄, MeasurableSet s → μ ((fun x => c • x) ⁻¹' s) = μ s
#align measure_theory.smul_invariant_measure MeasureTheory.SmulInvariantMeasure

namespace SmulInvariantMeasure

@[to_additive]
instance zero [MeasurableSpace α] [SMul M α] : SmulInvariantMeasure M α 0 :=
  ⟨fun _ _ _ => rfl⟩
#align measure_theory.smul_invariant_measure.zero MeasureTheory.SmulInvariantMeasure.zero

variable [SMul M α] {m : MeasurableSpace α} {μ ν : Measure α}

@[to_additive]
instance add [SmulInvariantMeasure M α μ] [SmulInvariantMeasure M α ν] :
    SmulInvariantMeasure M α (μ + ν) :=
  ⟨fun c s hs =>
    show _ + _ = _ + _ from
      congr_arg₂ (· + ·) (measure_preimage_smul μ c hs) (measure_preimage_smul ν c hs)⟩
#align measure_theory.smul_invariant_measure.add MeasureTheory.SmulInvariantMeasure.add

@[to_additive]
instance smul [SmulInvariantMeasure M α μ] (c : ℝ≥0∞) : SmulInvariantMeasure M α (c • μ) :=
  ⟨fun a s hs => show c • _ = c • _ from congr_arg ((· • ·) c) (measure_preimage_smul μ a hs)⟩
#align measure_theory.smul_invariant_measure.smul MeasureTheory.SmulInvariantMeasure.smul

@[to_additive]
instance smulNnreal [SmulInvariantMeasure M α μ] (c : ℝ≥0) : SmulInvariantMeasure M α (c • μ) :=
  SmulInvariantMeasure.smul c
#align
  measure_theory.smul_invariant_measure.smul_nnreal MeasureTheory.SmulInvariantMeasure.smulNnreal

end SmulInvariantMeasure

section HasMeasurableSmul

variable {m : MeasurableSpace α} [MeasurableSpace M] [SMul M α] [HasMeasurableSmul M α] (c : M)
  (μ : Measure α) [SmulInvariantMeasure M α μ]

@[simp, to_additive]
theorem measurePreservingSmul : MeasurePreserving ((· • ·) c) μ μ :=
  { Measurable := measurable_const_smul c
    map_eq := by
      ext1 s hs
      rw [map_apply (measurable_const_smul c) hs]
      exact smul_invariant_measure.measure_preimage_smul μ c hs }
#align measure_theory.measure_preserving_smul MeasureTheory.measurePreservingSmul

@[simp, to_additive]
theorem map_smul : map ((· • ·) c) μ = μ :=
  (measurePreservingSmul c μ).map_eq
#align measure_theory.map_smul MeasureTheory.map_smul

end HasMeasurableSmul

variable (G) {m : MeasurableSpace α} [Group G] [MulAction G α] [MeasurableSpace G]
  [HasMeasurableSmul G α] (c : G) (μ : Measure α)

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers
      [(Command.docComment
        "/--"
        "Equivalent definitions of a measure invariant under a multiplicative action of a group.\n\n- 0: `smul_invariant_measure G α μ`;\n\n- 1: for every `c : G` and a measurable set `s`, the measure of the preimage of `s` under scalar\n     multiplication by `c` is equal to the measure of `s`;\n\n- 2: for every `c : G` and a measurable set `s`, the measure of the image `c • s` of `s` under\n     scalar multiplication by `c` is equal to the measure of `s`;\n\n- 3, 4: properties 2, 3 for any set, including non-measurable ones;\n\n- 5: for any `c : G`, scalar multiplication by `c` maps `μ` to `μ`;\n\n- 6: for any `c : G`, scalar multiplication by `c` is a measure preserving map. -/")]
      [(Term.attributes
        "@["
        [(Term.attrInstance
          (Term.attrKind [])
          (to_additive "to_additive" [] [] (to_additiveRest [] [] [] [])))]
        "]")]
      []
      []
      []
      [])
     (Command.theorem
      "theorem"
      (Command.declId `smul_invariant_measure_tfae [])
      (Command.declSig
       []
       (Term.typeSpec
        ":"
        (Term.app
         `TFAE
         [(«term[_]»
           "["
           [(Term.app `SmulInvariantMeasure [`G `α `μ])
            ","
            (Term.forall
             "∀"
             [(Term.explicitBinder "(" [`c] [":" `G] [] ")")
              (Term.explicitBinder "(" [`s] [] [] ")")]
             []
             ","
             (Term.arrow
              (Term.app `MeasurableSet [`s])
              "→"
              («term_=_»
               (Term.app
                `μ
                [(Set.Data.Set.Image.«term_⁻¹'_»
                  (Term.app
                   (Term.paren
                    "("
                    (Algebra.Group.Defs.«term_•_» (Term.cdot "·") " • " (Term.cdot "·"))
                    ")")
                   [`c])
                  " ⁻¹' "
                  `s)])
               "="
               (Term.app `μ [`s]))))
            ","
            (Term.forall
             "∀"
             [(Term.explicitBinder "(" [`c] [":" `G] [] ")")
              (Term.explicitBinder "(" [`s] [] [] ")")]
             []
             ","
             (Term.arrow
              (Term.app `MeasurableSet [`s])
              "→"
              («term_=_»
               (Term.app `μ [(Algebra.Group.Defs.«term_•_» `c " • " `s)])
               "="
               (Term.app `μ [`s]))))
            ","
            (Term.forall
             "∀"
             [(Term.explicitBinder "(" [`c] [":" `G] [] ")")
              (Term.explicitBinder "(" [`s] [] [] ")")]
             []
             ","
             («term_=_»
              (Term.app
               `μ
               [(Set.Data.Set.Image.«term_⁻¹'_»
                 (Term.app
                  (Term.paren
                   "("
                   (Algebra.Group.Defs.«term_•_» (Term.cdot "·") " • " (Term.cdot "·"))
                   ")")
                  [`c])
                 " ⁻¹' "
                 `s)])
              "="
              (Term.app `μ [`s])))
            ","
            (Term.forall
             "∀"
             [(Term.explicitBinder "(" [`c] [":" `G] [] ")")
              (Term.explicitBinder "(" [`s] [] [] ")")]
             []
             ","
             («term_=_»
              (Term.app `μ [(Algebra.Group.Defs.«term_•_» `c " • " `s)])
              "="
              (Term.app `μ [`s])))
            ","
            (Term.forall
             "∀"
             [`c]
             [(Term.typeSpec ":" `G)]
             ","
             («term_=_»
              (Term.app
               `Measure.map
               [(Term.app
                 (Term.paren
                  "("
                  (Algebra.Group.Defs.«term_•_» (Term.cdot "·") " • " (Term.cdot "·"))
                  ")")
                 [`c])
                `μ])
              "="
              `μ))
            ","
            (Term.forall
             "∀"
             [`c]
             [(Term.typeSpec ":" `G)]
             ","
             (Term.app
              `MeasurePreserving
              [(Term.app
                (Term.paren
                 "("
                 (Algebra.Group.Defs.«term_•_» (Term.cdot "·") " • " (Term.cdot "·"))
                 ")")
                [`c])
               `μ
               `μ]))]
           "]")])))
      (Command.declValSimple
       ":="
       (Term.byTactic
        "by"
        (Tactic.tacticSeq
         (Tactic.tacticSeq1Indented
          [(Tactic.tfaeHave "tfae_have" [] (num "1") "↔" (num "2"))
           ";"
           (Tactic.exact
            "exact"
            (Term.anonymousCtor
             "⟨"
             [(Term.fun "fun" (Term.basicFun [`h] [] "=>" (Term.proj `h "." (fieldIdx "1"))))
              ","
              (Term.fun "fun" (Term.basicFun [`h] [] "=>" (Term.anonymousCtor "⟨" [`h] "⟩")))]
             "⟩"))
           []
           (Tactic.tfaeHave "tfae_have" [] (num "1") "→" (num "6"))
           ";"
           (tactic__
            (cdotTk (patternIgnore (token.«· » "·")))
            [(Tactic.intro "intro" [`h `c])
             []
             (Tactic.exact
              "exact"
              (Term.proj (Term.app `measure_preserving_smul [`c `μ]) "." `map_eq))])
           []
           (Tactic.tfaeHave "tfae_have" [] (num "6") "→" (num "7"))
           ";"
           (Tactic.exact
            "exact"
            (Term.fun
             "fun"
             (Term.basicFun
              [`H `c]
              []
              "=>"
              (Term.anonymousCtor
               "⟨"
               [(Term.app `measurable_const_smul [`c]) "," (Term.app `H [`c])]
               "⟩"))))
           []
           (Tactic.tfaeHave "tfae_have" [] (num "7") "→" (num "4"))
           ";"
           (Tactic.exact
            "exact"
            (Term.fun
             "fun"
             (Term.basicFun
              [`H `c]
              []
              "=>"
              (Term.app
               (Term.proj (Term.app `H [`c]) "." `measure_preimage_emb)
               [(Term.app `measurable_embedding_const_smul [`c])]))))
           []
           (Tactic.tfaeHave "tfae_have" [] (num "4") "→" (num "5"))
           ";"
           (Tactic.exact
            "exact"
            (Term.fun
             "fun"
             (Term.basicFun
              [`H `c `s]
              []
              "=>"
              (Term.byTactic
               "by"
               (Tactic.tacticSeq
                (Tactic.tacticSeq1Indented
                 [(Tactic.rwSeq
                   "rw"
                   []
                   (Tactic.rwRuleSeq
                    "["
                    [(Tactic.rwRule [(patternIgnore (token.«← » "←"))] `preimage_smul_inv)]
                    "]")
                   [])
                  []
                  (Tactic.apply "apply" `H)]))))))
           []
           (Tactic.tfaeHave "tfae_have" [] (num "5") "→" (num "3"))
           ";"
           (Tactic.exact
            "exact"
            (Term.fun "fun" (Term.basicFun [`H `c `s `hs] [] "=>" (Term.app `H [`c `s]))))
           []
           (Tactic.tfaeHave "tfae_have" [] (num "3") "→" (num "2"))
           ";"
           (tactic__
            (cdotTk (patternIgnore (token.«· » "·")))
            [(Tactic.intro "intro" [`H `c `s `hs])
             []
             (Tactic.rwSeq
              "rw"
              []
              (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `preimage_smul)] "]")
              [])
             []
             (Tactic.exact "exact" (Term.app `H [(«term_⁻¹» `c "⁻¹") `s `hs]))])
           []
           (Tactic.tfaeFinish "tfae_finish")])))
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
         [(Tactic.tfaeHave "tfae_have" [] (num "1") "↔" (num "2"))
          ";"
          (Tactic.exact
           "exact"
           (Term.anonymousCtor
            "⟨"
            [(Term.fun "fun" (Term.basicFun [`h] [] "=>" (Term.proj `h "." (fieldIdx "1"))))
             ","
             (Term.fun "fun" (Term.basicFun [`h] [] "=>" (Term.anonymousCtor "⟨" [`h] "⟩")))]
            "⟩"))
          []
          (Tactic.tfaeHave "tfae_have" [] (num "1") "→" (num "6"))
          ";"
          (tactic__
           (cdotTk (patternIgnore (token.«· » "·")))
           [(Tactic.intro "intro" [`h `c])
            []
            (Tactic.exact
             "exact"
             (Term.proj (Term.app `measure_preserving_smul [`c `μ]) "." `map_eq))])
          []
          (Tactic.tfaeHave "tfae_have" [] (num "6") "→" (num "7"))
          ";"
          (Tactic.exact
           "exact"
           (Term.fun
            "fun"
            (Term.basicFun
             [`H `c]
             []
             "=>"
             (Term.anonymousCtor
              "⟨"
              [(Term.app `measurable_const_smul [`c]) "," (Term.app `H [`c])]
              "⟩"))))
          []
          (Tactic.tfaeHave "tfae_have" [] (num "7") "→" (num "4"))
          ";"
          (Tactic.exact
           "exact"
           (Term.fun
            "fun"
            (Term.basicFun
             [`H `c]
             []
             "=>"
             (Term.app
              (Term.proj (Term.app `H [`c]) "." `measure_preimage_emb)
              [(Term.app `measurable_embedding_const_smul [`c])]))))
          []
          (Tactic.tfaeHave "tfae_have" [] (num "4") "→" (num "5"))
          ";"
          (Tactic.exact
           "exact"
           (Term.fun
            "fun"
            (Term.basicFun
             [`H `c `s]
             []
             "=>"
             (Term.byTactic
              "by"
              (Tactic.tacticSeq
               (Tactic.tacticSeq1Indented
                [(Tactic.rwSeq
                  "rw"
                  []
                  (Tactic.rwRuleSeq
                   "["
                   [(Tactic.rwRule [(patternIgnore (token.«← » "←"))] `preimage_smul_inv)]
                   "]")
                  [])
                 []
                 (Tactic.apply "apply" `H)]))))))
          []
          (Tactic.tfaeHave "tfae_have" [] (num "5") "→" (num "3"))
          ";"
          (Tactic.exact
           "exact"
           (Term.fun "fun" (Term.basicFun [`H `c `s `hs] [] "=>" (Term.app `H [`c `s]))))
          []
          (Tactic.tfaeHave "tfae_have" [] (num "3") "→" (num "2"))
          ";"
          (tactic__
           (cdotTk (patternIgnore (token.«· » "·")))
           [(Tactic.intro "intro" [`H `c `s `hs])
            []
            (Tactic.rwSeq "rw" [] (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `preimage_smul)] "]") [])
            []
            (Tactic.exact "exact" (Term.app `H [(«term_⁻¹» `c "⁻¹") `s `hs]))])
          []
          (Tactic.tfaeFinish "tfae_finish")])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.tfaeFinish "tfae_finish")
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (tactic__
       (cdotTk (patternIgnore (token.«· » "·")))
       [(Tactic.intro "intro" [`H `c `s `hs])
        []
        (Tactic.rwSeq "rw" [] (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `preimage_smul)] "]") [])
        []
        (Tactic.exact "exact" (Term.app `H [(«term_⁻¹» `c "⁻¹") `s `hs]))])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.exact "exact" (Term.app `H [(«term_⁻¹» `c "⁻¹") `s `hs]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `H [(«term_⁻¹» `c "⁻¹") `s `hs])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `hs
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `s
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_⁻¹»', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_⁻¹»', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      («term_⁻¹» `c "⁻¹")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `c
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `H
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.rwSeq "rw" [] (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `preimage_smul)] "]") [])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `preimage_smul
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.intro "intro" [`H `c `s `hs])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `hs
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `s
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `c
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `H
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.tfaeHave "tfae_have" [] (num "3") "→" (num "2"))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«→»', expected 'token.« → »'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«→»', expected 'token.« ↔ »'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«→»', expected 'token.« ← »'
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
      Equivalent definitions of a measure invariant under a multiplicative action of a group.
      
      - 0: `smul_invariant_measure G α μ`;
      
      - 1: for every `c : G` and a measurable set `s`, the measure of the preimage of `s` under scalar
           multiplication by `c` is equal to the measure of `s`;
      
      - 2: for every `c : G` and a measurable set `s`, the measure of the image `c • s` of `s` under
           scalar multiplication by `c` is equal to the measure of `s`;
      
      - 3, 4: properties 2, 3 for any set, including non-measurable ones;
      
      - 5: for any `c : G`, scalar multiplication by `c` maps `μ` to `μ`;
      
      - 6: for any `c : G`, scalar multiplication by `c` is a measure preserving map. -/
    @[ to_additive ]
  theorem
    smul_invariant_measure_tfae
    :
      TFAE
        [
          SmulInvariantMeasure G α μ
            ,
            ∀ ( c : G ) ( s ) , MeasurableSet s → μ ( · • · ) c ⁻¹' s = μ s
            ,
            ∀ ( c : G ) ( s ) , MeasurableSet s → μ c • s = μ s
            ,
            ∀ ( c : G ) ( s ) , μ ( · • · ) c ⁻¹' s = μ s
            ,
            ∀ ( c : G ) ( s ) , μ c • s = μ s
            ,
            ∀ c : G , Measure.map ( · • · ) c μ = μ
            ,
            ∀ c : G , MeasurePreserving ( · • · ) c μ μ
          ]
    :=
      by
        tfae_have 1 ↔ 2
          ;
          exact ⟨ fun h => h . 1 , fun h => ⟨ h ⟩ ⟩
          tfae_have 1 → 6
          ;
          · intro h c exact measure_preserving_smul c μ . map_eq
          tfae_have 6 → 7
          ;
          exact fun H c => ⟨ measurable_const_smul c , H c ⟩
          tfae_have 7 → 4
          ;
          exact fun H c => H c . measure_preimage_emb measurable_embedding_const_smul c
          tfae_have 4 → 5
          ;
          exact fun H c s => by rw [ ← preimage_smul_inv ] apply H
          tfae_have 5 → 3
          ;
          exact fun H c s hs => H c s
          tfae_have 3 → 2
          ;
          · intro H c s hs rw [ preimage_smul ] exact H c ⁻¹ s hs
          tfae_finish
#align measure_theory.smul_invariant_measure_tfae MeasureTheory.smul_invariant_measure_tfae

/-- Equivalent definitions of a measure invariant under an additive action of a group.

- 0: `vadd_invariant_measure G α μ`;

- 1: for every `c : G` and a measurable set `s`, the measure of the preimage of `s` under
     vector addition `(+ᵥ) c` is equal to the measure of `s`;

- 2: for every `c : G` and a measurable set `s`, the measure of the image `c +ᵥ s` of `s` under
     vector addition `(+ᵥ) c` is equal to the measure of `s`;

- 3, 4: properties 2, 3 for any set, including non-measurable ones;

- 5: for any `c : G`, vector addition of `c` maps `μ` to `μ`;

- 6: for any `c : G`, vector addition of `c` is a measure preserving map. -/
add_decl_doc vadd_invariant_measure_tfae

variable {G} [SmulInvariantMeasure G α μ]

@[simp, to_additive]
theorem measure_preimage_smul (s : Set α) : μ ((· • ·) c ⁻¹' s) = μ s :=
  ((smul_invariant_measure_tfae G μ).out 0 3).mp ‹_› c s
#align measure_theory.measure_preimage_smul MeasureTheory.measure_preimage_smul

@[simp, to_additive]
theorem measure_smul (s : Set α) : μ (c • s) = μ s :=
  ((smul_invariant_measure_tfae G μ).out 0 4).mp ‹_› c s
#align measure_theory.measure_smul MeasureTheory.measure_smul

variable {μ}

@[to_additive]
theorem NullMeasurableSet.smul {s} (hs : NullMeasurableSet s μ) (c : G) :
    NullMeasurableSet (c • s) μ := by
  simpa only [← preimage_smul_inv] using
    hs.preimage (measure_preserving_smul _ _).QuasiMeasurePreserving
#align measure_theory.null_measurable_set.smul MeasureTheory.NullMeasurableSet.smul

theorem measure_smul_null {s} (h : μ s = 0) (c : G) : μ (c • s) = 0 := by rwa [measure_smul]
#align measure_theory.measure_smul_null MeasureTheory.measure_smul_null

section IsMinimal

variable (G) [TopologicalSpace α] [HasContinuousConstSmul G α] [MulAction.IsMinimal G α]
  {K U : Set α}

/-- If measure `μ` is invariant under a group action and is nonzero on a compact set `K`, then it is
positive on any nonempty open set. In case of a regular measure, one can assume `μ ≠ 0` instead of
`μ K ≠ 0`, see `measure_theory.measure_is_open_pos_of_smul_invariant_of_ne_zero`. -/
@[to_additive]
theorem measure_is_open_pos_of_smul_invariant_of_compact_ne_zero (hK : IsCompact K) (hμK : μ K ≠ 0)
    (hU : IsOpen U) (hne : U.Nonempty) : 0 < μ U :=
  let ⟨t, ht⟩ := hK.exists_finite_cover_smul G hU hne
  pos_iff_ne_zero.2 fun hμU =>
    hμK <|
      measure_mono_null ht <|
        (measure_bUnion_null_iff t.countable_to_set).2 fun _ _ => by rwa [measure_smul]
#align
  measure_theory.measure_is_open_pos_of_smul_invariant_of_compact_ne_zero MeasureTheory.measure_is_open_pos_of_smul_invariant_of_compact_ne_zero

/-- If measure `μ` is invariant under an additive group action and is nonzero on a compact set `K`,
then it is positive on any nonempty open set. In case of a regular measure, one can assume `μ ≠ 0`
instead of `μ K ≠ 0`, see `measure_theory.measure_is_open_pos_of_vadd_invariant_of_ne_zero`. -/
add_decl_doc measure_is_open_pos_of_vadd_invariant_of_compact_ne_zero

@[to_additive]
theorem isLocallyFiniteMeasureOfSmulInvariant (hU : IsOpen U) (hne : U.Nonempty) (hμU : μ U ≠ ∞) :
    IsLocallyFiniteMeasure μ :=
  ⟨fun x =>
    let ⟨g, hg⟩ := hU.exists_smul_mem G x hne
    ⟨(· • ·) g ⁻¹' U, (hU.Preimage (continuous_id.const_smul _)).mem_nhds hg,
      Ne.lt_top <| by rwa [measure_preimage_smul]⟩⟩
#align
  measure_theory.is_locally_finite_measure_of_smul_invariant MeasureTheory.isLocallyFiniteMeasureOfSmulInvariant

variable [Measure.Regular μ]

@[to_additive]
theorem measure_is_open_pos_of_smul_invariant_of_ne_zero (hμ : μ ≠ 0) (hU : IsOpen U)
    (hne : U.Nonempty) : 0 < μ U :=
  let ⟨K, hK, hμK⟩ := Regular.exists_compact_not_null.mpr hμ
  measure_is_open_pos_of_smul_invariant_of_compact_ne_zero G hK hμK hU hne
#align
  measure_theory.measure_is_open_pos_of_smul_invariant_of_ne_zero MeasureTheory.measure_is_open_pos_of_smul_invariant_of_ne_zero

@[to_additive]
theorem measure_pos_iff_nonempty_of_smul_invariant (hμ : μ ≠ 0) (hU : IsOpen U) :
    0 < μ U ↔ U.Nonempty :=
  ⟨fun h => nonempty_of_measure_ne_zero h.ne',
    measure_is_open_pos_of_smul_invariant_of_ne_zero G hμ hU⟩
#align
  measure_theory.measure_pos_iff_nonempty_of_smul_invariant MeasureTheory.measure_pos_iff_nonempty_of_smul_invariant

include G

@[to_additive]
theorem measure_eq_zero_iff_eq_empty_of_smul_invariant (hμ : μ ≠ 0) (hU : IsOpen U) :
    μ U = 0 ↔ U = ∅ := by
  rw [← not_iff_not, ← Ne.def, ← pos_iff_ne_zero,
    measure_pos_iff_nonempty_of_smul_invariant G hμ hU, nonempty_iff_ne_empty]
#align
  measure_theory.measure_eq_zero_iff_eq_empty_of_smul_invariant MeasureTheory.measure_eq_zero_iff_eq_empty_of_smul_invariant

end IsMinimal

theorem smul_ae_eq_self_of_mem_zpowers {x y : G} (hs : (x • s : Set α) =ᵐ[μ] s)
    (hy : y ∈ Subgroup.zpowers x) : (y • s : Set α) =ᵐ[μ] s :=
  by
  obtain ⟨k, rfl⟩ := subgroup.mem_zpowers_iff.mp hy
  let e : α ≃ α := MulAction.toPermHom G α x
  have he : quasi_measure_preserving e μ μ := (measure_preserving_smul x μ).QuasiMeasurePreserving
  have he' : quasi_measure_preserving e.symm μ μ :=
    (measure_preserving_smul x⁻¹ μ).QuasiMeasurePreserving
  simpa only [MulAction.to_perm_hom_apply, MulAction.to_perm_apply, image_smul, ←
    MonoidHom.map_zpow] using he.image_zpow_ae_eq he' k hs
#align measure_theory.smul_ae_eq_self_of_mem_zpowers MeasureTheory.smul_ae_eq_self_of_mem_zpowers

theorem vadd_ae_eq_self_of_mem_zmultiples {G : Type _} [MeasurableSpace G] [AddGroup G]
    [AddAction G α] [VaddInvariantMeasure G α μ] [HasMeasurableVadd G α] {x y : G}
    (hs : (x +ᵥ s : Set α) =ᵐ[μ] s) (hy : y ∈ AddSubgroup.zmultiples x) :
    (y +ᵥ s : Set α) =ᵐ[μ] s :=
  by
  letI : MeasurableSpace (Multiplicative G) := (by infer_instance : MeasurableSpace G)
  letI : smul_invariant_measure (Multiplicative G) α μ :=
    ⟨fun g => vadd_invariant_measure.measure_preimage_vadd μ (Multiplicative.toAdd g)⟩
  letI : HasMeasurableSmul (Multiplicative G) α :=
    { measurable_const_smul := fun g => measurable_const_vadd (Multiplicative.toAdd g)
      measurable_smul_const := fun a =>
        @measurable_vadd_const (Multiplicative G) α (by infer_instance : VAdd G α) _ _
          (by infer_instance : HasMeasurableVadd G α) a }
  exact @smul_ae_eq_self_of_mem_zpowers (Multiplicative G) α _ _ _ _ _ _ _ _ _ _ hs hy
#align
  measure_theory.vadd_ae_eq_self_of_mem_zmultiples MeasureTheory.vadd_ae_eq_self_of_mem_zmultiples

attribute [to_additive vadd_ae_eq_self_of_mem_zmultiples] smul_ae_eq_self_of_mem_zpowers

end MeasureTheory

