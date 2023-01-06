/-
Copyright (c) 2021 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne, Sébastien Gouëzel

! This file was ported from Lean 3 source module measure_theory.function.strongly_measurable.inner
! leanprover-community/mathlib commit 18a5306c091183ac90884daa9373fa3b178e8607
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.MeasureTheory.Function.StronglyMeasurable.Basic
import Mathbin.Analysis.InnerProductSpace.Basic

/-!
# Inner products of strongly measurable functions are strongly measurable.

-/


variable {α : Type _}

namespace MeasureTheory

/-! ## Strongly measurable functions -/


namespace StronglyMeasurable

protected theorem inner {𝕜 : Type _} {E : Type _} [IsROrC 𝕜] [InnerProductSpace 𝕜 E]
    {m : MeasurableSpace α} {f g : α → E} (hf : StronglyMeasurable f) (hg : StronglyMeasurable g) :
    StronglyMeasurable fun t => @inner 𝕜 _ _ (f t) (g t) :=
  Continuous.comp_strongly_measurable continuous_inner (hf.prod_mk hg)
#align measure_theory.strongly_measurable.inner MeasureTheory.StronglyMeasurable.inner

end StronglyMeasurable

namespace AeStronglyMeasurable

variable {m : MeasurableSpace α} {μ : Measure α} {𝕜 : Type _} {E : Type _} [IsROrC 𝕜]
  [InnerProductSpace 𝕜 E]

-- mathport name: «expr⟪ , ⟫»
local notation "⟪" x ", " y "⟫" => @inner 𝕜 _ _ x y

protected theorem re {f : α → 𝕜} (hf : AeStronglyMeasurable f μ) :
    AeStronglyMeasurable (fun x => IsROrC.re (f x)) μ :=
  IsROrC.continuous_re.compAeStronglyMeasurable hf
#align measure_theory.ae_strongly_measurable.re MeasureTheory.AeStronglyMeasurable.re

protected theorem im {f : α → 𝕜} (hf : AeStronglyMeasurable f μ) :
    AeStronglyMeasurable (fun x => IsROrC.im (f x)) μ :=
  IsROrC.continuous_im.compAeStronglyMeasurable hf
#align measure_theory.ae_strongly_measurable.im MeasureTheory.AeStronglyMeasurable.im

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers [] [] [(Command.protected "protected")] [] [] [])
     (Command.theorem
      "theorem"
      (Command.declId `inner [])
      (Command.declSig
       [(Term.implicitBinder "{" [`m] [":" (Term.app `MeasurableSpace [`α])] "}")
        (Term.implicitBinder "{" [`μ] [":" (Term.app `Measure [`α])] "}")
        (Term.implicitBinder "{" [`f `g] [":" (Term.arrow `α "→" `E)] "}")
        (Term.explicitBinder "(" [`hf] [":" (Term.app `AeStronglyMeasurable [`f `μ])] [] ")")
        (Term.explicitBinder "(" [`hg] [":" (Term.app `AeStronglyMeasurable [`g `μ])] [] ")")]
       (Term.typeSpec
        ":"
        (Term.app
         `AeStronglyMeasurable
         [(Term.fun
           "fun"
           (Term.basicFun
            [`x]
            []
            "=>"
            (MeasureTheory.AeStronglyMeasurable.MeasureTheory.Function.StronglyMeasurable.Inner.«term⟪_,_⟫»
             "⟪"
             (Term.app `f [`x])
             ", "
             (Term.app `g [`x])
             "⟫")))
          `μ])))
      (Command.declValSimple
       ":="
       (Term.app
        (Term.proj `continuous_inner "." `compAeStronglyMeasurable)
        [(Term.app (Term.proj `hf "." `prod_mk) [`hg])])
       [])
      []
      []))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.abbrev'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.def'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       (Term.proj `continuous_inner "." `compAeStronglyMeasurable)
       [(Term.app (Term.proj `hf "." `prod_mk) [`hg])])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app (Term.proj `hf "." `prod_mk) [`hg])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `hg
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (Term.proj `hf "." `prod_mk)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `hf
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.app (Term.proj `hf "." `prod_mk) [`hg])
     ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (Term.proj `continuous_inner "." `compAeStronglyMeasurable)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `continuous_inner
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
      (Term.app
       `AeStronglyMeasurable
       [(Term.fun
         "fun"
         (Term.basicFun
          [`x]
          []
          "=>"
          (MeasureTheory.AeStronglyMeasurable.MeasureTheory.Function.StronglyMeasurable.Inner.«term⟪_,_⟫»
           "⟪"
           (Term.app `f [`x])
           ", "
           (Term.app `g [`x])
           "⟫")))
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
        (MeasureTheory.AeStronglyMeasurable.MeasureTheory.Function.StronglyMeasurable.Inner.«term⟪_,_⟫»
         "⟪"
         (Term.app `f [`x])
         ", "
         (Term.app `g [`x])
         "⟫")))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (MeasureTheory.AeStronglyMeasurable.MeasureTheory.Function.StronglyMeasurable.Inner.«term⟪_,_⟫»
       "⟪"
       (Term.app `f [`x])
       ", "
       (Term.app `g [`x])
       "⟫")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'MeasureTheory.AeStronglyMeasurable.MeasureTheory.Function.StronglyMeasurable.Inner.«term⟪_,_⟫»', expected 'MeasureTheory.AeStronglyMeasurable.MeasureTheory.Function.StronglyMeasurable.Inner.term⟪_,_⟫._@.MeasureTheory.Function.StronglyMeasurable.Inner._hyg.9'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.basicFun', expected 'Lean.Parser.Term.matchAlts'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.opaque'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.instance'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.axiom'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.example'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.inductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.classInductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.structure'-/-- failed to format: format: uncaught backtrack exception
protected
  theorem
    inner
    { m : MeasurableSpace α }
        { μ : Measure α }
        { f g : α → E }
        ( hf : AeStronglyMeasurable f μ )
        ( hg : AeStronglyMeasurable g μ )
      : AeStronglyMeasurable fun x => ⟪ f x , g x ⟫ μ
    := continuous_inner . compAeStronglyMeasurable hf . prod_mk hg
#align measure_theory.ae_strongly_measurable.inner MeasureTheory.AeStronglyMeasurable.inner

end AeStronglyMeasurable

end MeasureTheory

