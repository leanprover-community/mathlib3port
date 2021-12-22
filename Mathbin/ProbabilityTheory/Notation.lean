import Mathbin.MeasureTheory.Function.ConditionalExpectation

/-! # Notations for probability theory

This file defines the following notations, for functions `X,Y`, measures `P, Q` defined on a
measurable space `m0`, and another measurable space structure `m` with `hm : m ≤ m0`,
- `P[X] = ∫ a, X a ∂P`
- `𝔼[X] = ∫ a, X a`
- `𝔼[X|m,hm]`: conditional expectation of `X` with respect to the measure `volume` and the
  measurable space `m`. The similar `P[X|m,hm]` for a measure `P` is defined in
  measure_theory.function.conditional_expectation.
- `X =ₐₛ Y`: `X =ᵐ[volume] Y`
- `X ≤ₐₛ Y`: `X ≤ᵐ[volume] Y`
- `∂P/∂Q = P.rn_deriv Q`
We note that the notation `∂P/∂Q` applies to three different cases, namely,
`measure_theory.measure.rn_deriv`, `measure_theory.signed_measure.rn_deriv` and
`measure_theory.complex_measure.rn_deriv`.

TODO: define the notation `ℙ s` for the probability of a set `s`, and decide whether it should be a
value in `ℝ`, `ℝ≥0` or `ℝ≥0∞`.
-/


open MeasureTheory

localized [ProbabilityTheory] notation "𝔼[" X "|" hm "]" => MeasureTheory.condexp _ hm MeasureTheory.Measure.volume X

localized [ProbabilityTheory]
  notation "𝔼[" X "|" m "," hm "]" => MeasureTheory.condexp m hm MeasureTheory.Measure.volume X

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.localized
 "localized"
 "["
 `ProbabilityTheory
 "]"
 (Command.notation
  (Term.attrKind [])
  "notation"
  []
  []
  []
  [(Command.identPrec `P []) (strLit "\"[\"") (Command.identPrec `X []) (strLit "\"]\"")]
  "=>"
  (MeasureTheory.MeasureTheory.Integral.Bochner.«term∫_,_∂_»
   "∫"
   (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `x)] []))
   ", "
   (Term.app `X [`x])
   " ∂"
   `P)))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.localized', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.notation', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.notation', expected 'Lean.Parser.Command.notation.antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (MeasureTheory.MeasureTheory.Integral.Bochner.«term∫_,_∂_»
   "∫"
   (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `x)] []))
   ", "
   (Term.app `X [`x])
   " ∂"
   `P)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'MeasureTheory.MeasureTheory.Integral.Bochner.«term∫_,_∂_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `P
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.app `X [`x])
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
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `X
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.explicitBinders', expected 'Mathlib.ExtendedBinder.extBinders'-/-- failed to format: format: uncaught backtrack exception
localized [ ProbabilityTheory ] notation P "[" X "]" => ∫ x , X x ∂ P

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.localized
 "localized"
 "["
 `ProbabilityTheory
 "]"
 (Command.notation
  (Term.attrKind [])
  "notation"
  []
  []
  []
  [(strLit "\"𝔼[\"") (Command.identPrec `X []) (strLit "\"]\"")]
  "=>"
  (MeasureTheory.MeasureTheory.Integral.Bochner.«term∫_,_»
   "∫"
   (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `a)] []))
   ", "
   (Term.app `X [`a]))))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.localized', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.notation', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.notation', expected 'Lean.Parser.Command.notation.antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (MeasureTheory.MeasureTheory.Integral.Bochner.«term∫_,_»
   "∫"
   (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `a)] []))
   ", "
   (Term.app `X [`a]))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'MeasureTheory.MeasureTheory.Integral.Bochner.«term∫_,_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.app `X [`a])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `a
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `X
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.explicitBinders', expected 'Mathlib.ExtendedBinder.extBinders'-/-- failed to format: format: uncaught backtrack exception
localized [ ProbabilityTheory ] notation "𝔼[" X "]" => ∫ a , X a

localized [ProbabilityTheory] notation:50 X "=ₐₛ" Y:50 => X =ᵐ[MeasureTheory.Measure.volume] Y

localized [ProbabilityTheory] notation:50 X "≤ₐₛ" Y:50 => X ≤ᵐ[MeasureTheory.Measure.volume] Y

localized [ProbabilityTheory] notation "∂" P "/∂" Q:50 => P.rn_deriv Q

