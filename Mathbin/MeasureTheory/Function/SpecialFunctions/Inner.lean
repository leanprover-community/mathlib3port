/-
Copyright (c) 2020 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov

! This file was ported from Lean 3 source module measure_theory.function.special_functions.inner
! leanprover-community/mathlib commit 6d0adfa76594f304b4650d098273d4366edeb61b
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Analysis.InnerProductSpace.Basic
import Mathbin.MeasureTheory.Constructions.BorelSpace

/-!
# Measurability of scalar products
-/


variable {α : Type _} {𝕜 : Type _} {E : Type _} [IsROrC 𝕜] [InnerProductSpace 𝕜 E]

-- mathport name: «expr⟪ , ⟫»
local notation "⟪" x ", " y "⟫" => @inner 𝕜 _ _ x y

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers
      []
      [(Term.attributes
        "@["
        [(Term.attrInstance (Term.attrKind []) (Attr.simple `measurability []))]
        "]")]
      []
      []
      []
      [])
     (Command.theorem
      "theorem"
      (Command.declId `Measurable.inner [])
      (Command.declSig
       [(Term.implicitBinder "{" [`m] [":" (Term.app `MeasurableSpace [`α])] "}")
        (Term.instBinder "[" [] (Term.app `MeasurableSpace [`E]) "]")
        (Term.instBinder "[" [] (Term.app `OpensMeasurableSpace [`E]) "]")
        (Term.instBinder "[" [] (Term.app `TopologicalSpace.SecondCountableTopology [`E]) "]")
        (Term.implicitBinder "{" [`f `g] [":" (Term.arrow `α "→" `E)] "}")
        (Term.explicitBinder "(" [`hf] [":" (Term.app `Measurable [`f])] [] ")")
        (Term.explicitBinder "(" [`hg] [":" (Term.app `Measurable [`g])] [] ")")]
       (Term.typeSpec
        ":"
        (Term.app
         `Measurable
         [(Term.fun
           "fun"
           (Term.basicFun
            [`t]
            []
            "=>"
            (MeasureTheory.Function.SpecialFunctions.Inner.«term⟪_,_⟫»
             "⟪"
             (Term.app `f [`t])
             ", "
             (Term.app `g [`t])
             "⟫")))])))
      (Command.declValSimple ":=" (Term.app `Continuous.measurable2 [`continuous_inner `hf `hg]) [])
      []
      []))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.abbrev'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.def'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `Continuous.measurable2 [`continuous_inner `hf `hg])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `hg
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `hf
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `continuous_inner
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `Continuous.measurable2
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
      (Term.app
       `Measurable
       [(Term.fun
         "fun"
         (Term.basicFun
          [`t]
          []
          "=>"
          (MeasureTheory.Function.SpecialFunctions.Inner.«term⟪_,_⟫»
           "⟪"
           (Term.app `f [`t])
           ", "
           (Term.app `g [`t])
           "⟫")))])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.fun
       "fun"
       (Term.basicFun
        [`t]
        []
        "=>"
        (MeasureTheory.Function.SpecialFunctions.Inner.«term⟪_,_⟫»
         "⟪"
         (Term.app `f [`t])
         ", "
         (Term.app `g [`t])
         "⟫")))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (MeasureTheory.Function.SpecialFunctions.Inner.«term⟪_,_⟫»
       "⟪"
       (Term.app `f [`t])
       ", "
       (Term.app `g [`t])
       "⟫")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'MeasureTheory.Function.SpecialFunctions.Inner.«term⟪_,_⟫»', expected 'MeasureTheory.Function.SpecialFunctions.Inner.term⟪_,_⟫._@.MeasureTheory.Function.SpecialFunctions.Inner._hyg.5'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.basicFun', expected 'Lean.Parser.Term.matchAlts'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.opaque'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.instance'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.axiom'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.example'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.inductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.classInductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.structure'-/-- failed to format: format: uncaught backtrack exception
@[ measurability ]
  theorem
    Measurable.inner
    { m : MeasurableSpace α }
        [ MeasurableSpace E ]
        [ OpensMeasurableSpace E ]
        [ TopologicalSpace.SecondCountableTopology E ]
        { f g : α → E }
        ( hf : Measurable f )
        ( hg : Measurable g )
      : Measurable fun t => ⟪ f t , g t ⟫
    := Continuous.measurable2 continuous_inner hf hg
#align measurable.inner Measurable.inner

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers
      []
      [(Term.attributes
        "@["
        [(Term.attrInstance (Term.attrKind []) (Attr.simple `measurability []))]
        "]")]
      []
      []
      []
      [])
     (Command.theorem
      "theorem"
      (Command.declId `AeMeasurable.inner [])
      (Command.declSig
       [(Term.implicitBinder "{" [`m] [":" (Term.app `MeasurableSpace [`α])] "}")
        (Term.instBinder "[" [] (Term.app `MeasurableSpace [`E]) "]")
        (Term.instBinder "[" [] (Term.app `OpensMeasurableSpace [`E]) "]")
        (Term.instBinder "[" [] (Term.app `TopologicalSpace.SecondCountableTopology [`E]) "]")
        (Term.implicitBinder "{" [`μ] [":" (Term.app `MeasureTheory.Measure [`α])] "}")
        (Term.implicitBinder "{" [`f `g] [":" (Term.arrow `α "→" `E)] "}")
        (Term.explicitBinder "(" [`hf] [":" (Term.app `AeMeasurable [`f `μ])] [] ")")
        (Term.explicitBinder "(" [`hg] [":" (Term.app `AeMeasurable [`g `μ])] [] ")")]
       (Term.typeSpec
        ":"
        (Term.app
         `AeMeasurable
         [(Term.fun
           "fun"
           (Term.basicFun
            [`x]
            []
            "=>"
            (MeasureTheory.Function.SpecialFunctions.Inner.«term⟪_,_⟫»
             "⟪"
             (Term.app `f [`x])
             ", "
             (Term.app `g [`x])
             "⟫")))
          `μ])))
      (Command.declValSimple
       ":="
       (Term.byTactic
        "by"
        (Tactic.tacticSeq
         (Tactic.tacticSeq1Indented
          [(Tactic.refine'
            "refine'"
            (Term.anonymousCtor
             "⟨"
             [(Term.fun
               "fun"
               (Term.basicFun
                [`x]
                []
                "=>"
                (MeasureTheory.Function.SpecialFunctions.Inner.«term⟪_,_⟫»
                 "⟪"
                 (Term.app `hf.mk [`f `x])
                 ", "
                 (Term.app `hg.mk [`g `x])
                 "⟫")))
              ","
              (Term.app `hf.measurable_mk.inner [`hg.measurable_mk])
              ","
              (Term.hole "_")]
             "⟩"))
           []
           (Tactic.refine'
            "refine'"
            (Term.app
             `hf.ae_eq_mk.mp
             [(Term.app
               `hg.ae_eq_mk.mono
               [(Term.fun "fun" (Term.basicFun [`x `hxg `hxf] [] "=>" (Term.hole "_")))])]))
           []
           (Tactic.dsimp "dsimp" [] [] ["only"] [] [])
           []
           (Tactic.congr "congr" [])
           []
           (Std.Tactic.exacts "exacts" "[" [`hxf "," `hxg] "]")])))
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
           (Term.anonymousCtor
            "⟨"
            [(Term.fun
              "fun"
              (Term.basicFun
               [`x]
               []
               "=>"
               (MeasureTheory.Function.SpecialFunctions.Inner.«term⟪_,_⟫»
                "⟪"
                (Term.app `hf.mk [`f `x])
                ", "
                (Term.app `hg.mk [`g `x])
                "⟫")))
             ","
             (Term.app `hf.measurable_mk.inner [`hg.measurable_mk])
             ","
             (Term.hole "_")]
            "⟩"))
          []
          (Tactic.refine'
           "refine'"
           (Term.app
            `hf.ae_eq_mk.mp
            [(Term.app
              `hg.ae_eq_mk.mono
              [(Term.fun "fun" (Term.basicFun [`x `hxg `hxf] [] "=>" (Term.hole "_")))])]))
          []
          (Tactic.dsimp "dsimp" [] [] ["only"] [] [])
          []
          (Tactic.congr "congr" [])
          []
          (Std.Tactic.exacts "exacts" "[" [`hxf "," `hxg] "]")])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Std.Tactic.exacts "exacts" "[" [`hxf "," `hxg] "]")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `hxg
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `hxf
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.congr "congr" [])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.dsimp "dsimp" [] [] ["only"] [] [])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.refine'
       "refine'"
       (Term.app
        `hf.ae_eq_mk.mp
        [(Term.app
          `hg.ae_eq_mk.mono
          [(Term.fun "fun" (Term.basicFun [`x `hxg `hxf] [] "=>" (Term.hole "_")))])]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       `hf.ae_eq_mk.mp
       [(Term.app
         `hg.ae_eq_mk.mono
         [(Term.fun "fun" (Term.basicFun [`x `hxg `hxf] [] "=>" (Term.hole "_")))])])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       `hg.ae_eq_mk.mono
       [(Term.fun "fun" (Term.basicFun [`x `hxg `hxf] [] "=>" (Term.hole "_")))])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.fun "fun" (Term.basicFun [`x `hxg `hxf] [] "=>" (Term.hole "_")))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.strictImplicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.implicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.instBinder'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `hxf
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.strictImplicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.implicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.instBinder'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `hxg
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
      `hg.ae_eq_mk.mono
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.app
      `hg.ae_eq_mk.mono
      [(Term.fun "fun" (Term.basicFun [`x `hxg `hxf] [] "=>" (Term.hole "_")))])
     ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `hf.ae_eq_mk.mp
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
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
           (MeasureTheory.Function.SpecialFunctions.Inner.«term⟪_,_⟫»
            "⟪"
            (Term.app `hf.mk [`f `x])
            ", "
            (Term.app `hg.mk [`g `x])
            "⟫")))
         ","
         (Term.app `hf.measurable_mk.inner [`hg.measurable_mk])
         ","
         (Term.hole "_")]
        "⟩"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.anonymousCtor
       "⟨"
       [(Term.fun
         "fun"
         (Term.basicFun
          [`x]
          []
          "=>"
          (MeasureTheory.Function.SpecialFunctions.Inner.«term⟪_,_⟫»
           "⟪"
           (Term.app `hf.mk [`f `x])
           ", "
           (Term.app `hg.mk [`g `x])
           "⟫")))
        ","
        (Term.app `hf.measurable_mk.inner [`hg.measurable_mk])
        ","
        (Term.hole "_")]
       "⟩")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `hf.measurable_mk.inner [`hg.measurable_mk])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `hg.measurable_mk
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `hf.measurable_mk.inner
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
        (MeasureTheory.Function.SpecialFunctions.Inner.«term⟪_,_⟫»
         "⟪"
         (Term.app `hf.mk [`f `x])
         ", "
         (Term.app `hg.mk [`g `x])
         "⟫")))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (MeasureTheory.Function.SpecialFunctions.Inner.«term⟪_,_⟫»
       "⟪"
       (Term.app `hf.mk [`f `x])
       ", "
       (Term.app `hg.mk [`g `x])
       "⟫")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'MeasureTheory.Function.SpecialFunctions.Inner.«term⟪_,_⟫»', expected 'MeasureTheory.Function.SpecialFunctions.Inner.term⟪_,_⟫._@.MeasureTheory.Function.SpecialFunctions.Inner._hyg.5'
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
@[ measurability ]
  theorem
    AeMeasurable.inner
    { m : MeasurableSpace α }
        [ MeasurableSpace E ]
        [ OpensMeasurableSpace E ]
        [ TopologicalSpace.SecondCountableTopology E ]
        { μ : MeasureTheory.Measure α }
        { f g : α → E }
        ( hf : AeMeasurable f μ )
        ( hg : AeMeasurable g μ )
      : AeMeasurable fun x => ⟪ f x , g x ⟫ μ
    :=
      by
        refine' ⟨ fun x => ⟪ hf.mk f x , hg.mk g x ⟫ , hf.measurable_mk.inner hg.measurable_mk , _ ⟩
          refine' hf.ae_eq_mk.mp hg.ae_eq_mk.mono fun x hxg hxf => _
          dsimp only
          congr
          exacts [ hxf , hxg ]
#align ae_measurable.inner AeMeasurable.inner

