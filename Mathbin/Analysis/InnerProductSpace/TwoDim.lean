/-
Copyright (c) 2022 Heather Macbeth. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Heather Macbeth

! This file was ported from Lean 3 source module analysis.inner_product_space.two_dim
! leanprover-community/mathlib commit 5a3e819569b0f12cbec59d740a2613018e7b8eec
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Analysis.InnerProductSpace.Dual
import Mathbin.Analysis.InnerProductSpace.Orientation
import Mathbin.Tactic.LinearCombination

/-!
# Oriented two-dimensional real inner product spaces

This file defines constructions specific to the geometry of an oriented two-dimensional real inner
product space `E`.

## Main declarations

* `orientation.area_form`: an antisymmetric bilinear form `E →ₗ[ℝ] E →ₗ[ℝ] ℝ` (usual notation `ω`).
  Morally, when `ω` is evaluated on two vectors, it gives the oriented area of the parallelogram
  they span. (But mathlib does not yet have a construction of oriented area, and in fact the
  construction of oriented area should pass through `ω`.)

* `orientation.right_angle_rotation`: an isometric automorphism `E ≃ₗᵢ[ℝ] E` (usual notation `J`).
  This automorphism squares to -1.  In a later file, rotations (`orientation.rotation`) are defined,
  in such a way that this automorphism is equal to rotation by 90 degrees.

* `orientation.basis_right_angle_rotation`: for a nonzero vector `x` in `E`, the basis `![x, J x]`
  for `E`.

* `orientation.kahler`: a complex-valued real-bilinear map `E →ₗ[ℝ] E →ₗ[ℝ] ℂ`. Its real part is the
  inner product and its imaginary part is `orientation.area_form`.  For vectors `x` and `y` in `E`,
  the complex number `o.kahler x y` has modulus `‖x‖ * ‖y‖`. In a later file, oriented angles
  (`orientation.oangle`) are defined, in such a way that the argument of `o.kahler x y` is the
  oriented angle from `x` to `y`.

## Main results

* `orientation.right_angle_rotation_right_angle_rotation`: the identity `J (J x) = - x`

* `orientation.nonneg_inner_and_area_form_eq_zero_iff_same_ray`: `x`, `y` are in the same ray, if
  and only if `0 ≤ ⟪x, y⟫` and `ω x y = 0`

* `orientation.kahler_mul`: the identity `o.kahler x a * o.kahler a y = ‖a‖ ^ 2 * o.kahler x y`

* `complex.area_form`, `complex.right_angle_rotation`, `complex.kahler`: the concrete
  interpretations of `area_form`, `right_angle_rotation`, `kahler` for the oriented real inner
  product space `ℂ`

* `orientation.area_form_map_complex`, `orientation.right_angle_rotation_map_complex`,
  `orientation.kahler_map_complex`: given an orientation-preserving isometry from `E` to `ℂ`,
  expressions for `area_form`, `right_angle_rotation`, `kahler` as the pullback of their concrete
  interpretations on `ℂ`

## Implementation notes

Notation `ω` for `orientation.area_form` and `J` for `orientation.right_angle_rotation` should be
defined locally in each file which uses them, since otherwise one would need a more cumbersome
notation which mentions the orientation explicitly (something like `ω[o]`).  Write

```
local notation `ω` := o.area_form
local notation `J` := o.right_angle_rotation
```

-/


noncomputable section

open RealInnerProductSpace ComplexConjugate

open FiniteDimensional

attribute [local instance] fact_finite_dimensional_of_finrank_eq_succ

variable {E : Type _} [InnerProductSpace ℝ E] [Fact (finrank ℝ E = 2)] (o : Orientation ℝ E (Fin 2))

namespace Orientation

include o

/-- An antisymmetric bilinear form on an oriented real inner product space of dimension 2 (usual
notation `ω`).  When evaluated on two vectors, it gives the oriented area of the parallelogram they
span. -/
irreducible_def areaForm : E →ₗ[ℝ] E →ₗ[ℝ] ℝ :=
  by
  let z : AlternatingMap ℝ E ℝ (Fin 0) ≃ₗ[ℝ] ℝ :=
    alternating_map.const_linear_equiv_of_is_empty.symm
  let y : AlternatingMap ℝ E ℝ (Fin 1) →ₗ[ℝ] E →ₗ[ℝ] ℝ :=
    LinearMap.llcomp ℝ E (AlternatingMap ℝ E ℝ (Fin 0)) ℝ z ∘ₗ AlternatingMap.curryLeftLinearMap
  exact y ∘ₗ AlternatingMap.curryLeftLinearMap o.volume_form
#align orientation.area_form Orientation.areaForm

omit o

-- mathport name: exprω
local notation "ω" => o.areaForm

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers [] [] [] [] [] [])
     (Command.theorem
      "theorem"
      (Command.declId `area_form_to_volume_form [])
      (Command.declSig
       [(Term.explicitBinder "(" [`x `y] [":" `E] [] ")")]
       (Term.typeSpec
        ":"
        («term_=_»
         (Term.app (Orientation.Analysis.InnerProductSpace.TwoDim.termω "ω") [`x `y])
         "="
         (Term.app
          (Term.proj `o "." `volumeForm)
          [(Matrix.Data.Fin.VecNotation.«term![_,» "![" [`x "," `y] "]")]))))
      (Command.declValSimple
       ":="
       (Term.byTactic
        "by"
        (Tactic.tacticSeq
         (Tactic.tacticSeq1Indented
          [(Tactic.simp "simp" [] [] [] ["[" [(Tactic.simpLemma [] [] `area_form)] "]"] [])])))
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
         [(Tactic.simp "simp" [] [] [] ["[" [(Tactic.simpLemma [] [] `area_form)] "]"] [])])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.simp "simp" [] [] [] ["[" [(Tactic.simpLemma [] [] `area_form)] "]"] [])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `area_form
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, tactic) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
      («term_=_»
       (Term.app (Orientation.Analysis.InnerProductSpace.TwoDim.termω "ω") [`x `y])
       "="
       (Term.app
        (Term.proj `o "." `volumeForm)
        [(Matrix.Data.Fin.VecNotation.«term![_,» "![" [`x "," `y] "]")]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       (Term.proj `o "." `volumeForm)
       [(Matrix.Data.Fin.VecNotation.«term![_,» "![" [`x "," `y] "]")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Matrix.Data.Fin.VecNotation.«term![_,»', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Matrix.Data.Fin.VecNotation.«term![_,»', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Matrix.Data.Fin.VecNotation.«term![_,» "![" [`x "," `y] "]")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `y
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `x
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (Term.proj `o "." `volumeForm)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `o
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 50, term))
      (Term.app (Orientation.Analysis.InnerProductSpace.TwoDim.termω "ω") [`x `y])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `y
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `x
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (Orientation.Analysis.InnerProductSpace.TwoDim.termω "ω")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Orientation.Analysis.InnerProductSpace.TwoDim.termω', expected 'Orientation.Analysis.InnerProductSpace.TwoDim.termω._@.Analysis.InnerProductSpace.TwoDim._hyg.7'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.opaque'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.instance'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.axiom'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.example'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.inductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.classInductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.structure'-/-- failed to format: format: uncaught backtrack exception
theorem
  area_form_to_volume_form
  ( x y : E ) : ω x y = o . volumeForm ![ x , y ]
  := by simp [ area_form ]
#align orientation.area_form_to_volume_form Orientation.area_form_to_volume_form

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers
      []
      [(Term.attributes "@[" [(Term.attrInstance (Term.attrKind []) (Attr.simp "simp" [] []))] "]")]
      []
      []
      []
      [])
     (Command.theorem
      "theorem"
      (Command.declId `area_form_apply_self [])
      (Command.declSig
       [(Term.explicitBinder "(" [`x] [":" `E] [] ")")]
       (Term.typeSpec
        ":"
        («term_=_»
         (Term.app (Orientation.Analysis.InnerProductSpace.TwoDim.termω "ω") [`x `x])
         "="
         (num "0"))))
      (Command.declValSimple
       ":="
       (Term.byTactic
        "by"
        (Tactic.tacticSeq
         (Tactic.tacticSeq1Indented
          [(Tactic.rwSeq
            "rw"
            []
            (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `area_form_to_volume_form)] "]")
            [])
           []
           (Tactic.refine'
            "refine'"
            (Term.app
             `o.volume_form.map_eq_zero_of_eq
             [(Matrix.Data.Fin.VecNotation.«term![_,» "![" [`x "," `x] "]")
              (Term.hole "_")
              (Term.typeAscription
               "("
               (Term.hole "_")
               ":"
               [(«term_≠_»
                 (Term.typeAscription "(" (num "0") ":" [(Term.app `Fin [(num "2")])] ")")
                 "≠"
                 (num "1"))]
               ")")]))
           []
           (tactic__
            (cdotTk (patternIgnore (token.«· » "·")))
            [(Tactic.simp "simp" [] [] [] [] [])])
           []
           (tactic__
            (cdotTk (patternIgnore (token.«· » "·")))
            [(Mathlib.Tactic.normNum "norm_num" [] [] [])])])))
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
           (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `area_form_to_volume_form)] "]")
           [])
          []
          (Tactic.refine'
           "refine'"
           (Term.app
            `o.volume_form.map_eq_zero_of_eq
            [(Matrix.Data.Fin.VecNotation.«term![_,» "![" [`x "," `x] "]")
             (Term.hole "_")
             (Term.typeAscription
              "("
              (Term.hole "_")
              ":"
              [(«term_≠_»
                (Term.typeAscription "(" (num "0") ":" [(Term.app `Fin [(num "2")])] ")")
                "≠"
                (num "1"))]
              ")")]))
          []
          (tactic__ (cdotTk (patternIgnore (token.«· » "·"))) [(Tactic.simp "simp" [] [] [] [] [])])
          []
          (tactic__
           (cdotTk (patternIgnore (token.«· » "·")))
           [(Mathlib.Tactic.normNum "norm_num" [] [] [])])])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (tactic__
       (cdotTk (patternIgnore (token.«· » "·")))
       [(Mathlib.Tactic.normNum "norm_num" [] [] [])])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Mathlib.Tactic.normNum "norm_num" [] [] [])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (tactic__ (cdotTk (patternIgnore (token.«· » "·"))) [(Tactic.simp "simp" [] [] [] [] [])])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.simp "simp" [] [] [] [] [])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.refine'
       "refine'"
       (Term.app
        `o.volume_form.map_eq_zero_of_eq
        [(Matrix.Data.Fin.VecNotation.«term![_,» "![" [`x "," `x] "]")
         (Term.hole "_")
         (Term.typeAscription
          "("
          (Term.hole "_")
          ":"
          [(«term_≠_»
            (Term.typeAscription "(" (num "0") ":" [(Term.app `Fin [(num "2")])] ")")
            "≠"
            (num "1"))]
          ")")]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       `o.volume_form.map_eq_zero_of_eq
       [(Matrix.Data.Fin.VecNotation.«term![_,» "![" [`x "," `x] "]")
        (Term.hole "_")
        (Term.typeAscription
         "("
         (Term.hole "_")
         ":"
         [(«term_≠_»
           (Term.typeAscription "(" (num "0") ":" [(Term.app `Fin [(num "2")])] ")")
           "≠"
           (num "1"))]
         ")")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.typeAscription', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.typeAscription', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.typeAscription
       "("
       (Term.hole "_")
       ":"
       [(«term_≠_»
         (Term.typeAscription "(" (num "0") ":" [(Term.app `Fin [(num "2")])] ")")
         "≠"
         (num "1"))]
       ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_≠_»
       (Term.typeAscription "(" (num "0") ":" [(Term.app `Fin [(num "2")])] ")")
       "≠"
       (num "1"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (num "1")
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 50, term))
      (Term.typeAscription "(" (num "0") ":" [(Term.app `Fin [(num "2")])] ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `Fin [(num "2")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'num', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'num', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (num "2")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `Fin
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (num "0")
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1024, (none, [anonymous]) <=? (some 50, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 50, (some 51, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, term))
      (Term.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1023, term)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Matrix.Data.Fin.VecNotation.«term![_,»', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Matrix.Data.Fin.VecNotation.«term![_,»', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, term))
      (Matrix.Data.Fin.VecNotation.«term![_,» "![" [`x "," `x] "]")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `x
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `x
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1023, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `o.volume_form.map_eq_zero_of_eq
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.rwSeq
       "rw"
       []
       (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `area_form_to_volume_form)] "]")
       [])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `area_form_to_volume_form
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, tactic) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
      («term_=_»
       (Term.app (Orientation.Analysis.InnerProductSpace.TwoDim.termω "ω") [`x `x])
       "="
       (num "0"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (num "0")
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 50, term))
      (Term.app (Orientation.Analysis.InnerProductSpace.TwoDim.termω "ω") [`x `x])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `x
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `x
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (Orientation.Analysis.InnerProductSpace.TwoDim.termω "ω")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Orientation.Analysis.InnerProductSpace.TwoDim.termω', expected 'Orientation.Analysis.InnerProductSpace.TwoDim.termω._@.Analysis.InnerProductSpace.TwoDim._hyg.7'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.opaque'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.instance'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.axiom'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.example'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.inductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.classInductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.structure'-/-- failed to format: format: uncaught backtrack exception
@[ simp ]
  theorem
    area_form_apply_self
    ( x : E ) : ω x x = 0
    :=
      by
        rw [ area_form_to_volume_form ]
          refine' o.volume_form.map_eq_zero_of_eq ![ x , x ] _ ( _ : ( 0 : Fin 2 ) ≠ 1 )
          · simp
          · norm_num
#align orientation.area_form_apply_self Orientation.area_form_apply_self

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers [] [] [] [] [] [])
     (Command.theorem
      "theorem"
      (Command.declId `area_form_swap [])
      (Command.declSig
       [(Term.explicitBinder "(" [`x `y] [":" `E] [] ")")]
       (Term.typeSpec
        ":"
        («term_=_»
         (Term.app (Orientation.Analysis.InnerProductSpace.TwoDim.termω "ω") [`x `y])
         "="
         («term-_»
          "-"
          (Term.app (Orientation.Analysis.InnerProductSpace.TwoDim.termω "ω") [`y `x])))))
      (Command.declValSimple
       ":="
       (Term.byTactic
        "by"
        (Tactic.tacticSeq
         (Tactic.tacticSeq1Indented
          [(Tactic.simp
            "simp"
            []
            []
            ["only"]
            ["[" [(Tactic.simpLemma [] [] `area_form_to_volume_form)] "]"]
            [])
           []
           (convert
            "convert"
            []
            (Term.app
             `o.volume_form.map_swap
             [(Matrix.Data.Fin.VecNotation.«term![_,» "![" [`y "," `x] "]")
              (Term.typeAscription
               "("
               (Term.hole "_")
               ":"
               [(«term_≠_»
                 (Term.typeAscription "(" (num "0") ":" [(Term.app `Fin [(num "2")])] ")")
                 "≠"
                 (num "1"))]
               ")")])
            [])
           []
           (tactic__
            (cdotTk (patternIgnore (token.«· » "·")))
            [(Std.Tactic.Ext.«tacticExt___:_»
              "ext"
              [(Std.Tactic.RCases.rintroPat.one (Std.Tactic.RCases.rcasesPat.one `i))]
              [])
             []
             (Tactic.«tactic_<;>_»
              (Lean.Elab.Tactic.finCases "fin_cases" [`i] [])
              "<;>"
              (Tactic.tacticRfl "rfl"))])
           []
           (tactic__
            (cdotTk (patternIgnore (token.«· » "·")))
            [(Mathlib.Tactic.normNum "norm_num" [] [] [])])])))
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
         [(Tactic.simp
           "simp"
           []
           []
           ["only"]
           ["[" [(Tactic.simpLemma [] [] `area_form_to_volume_form)] "]"]
           [])
          []
          (convert
           "convert"
           []
           (Term.app
            `o.volume_form.map_swap
            [(Matrix.Data.Fin.VecNotation.«term![_,» "![" [`y "," `x] "]")
             (Term.typeAscription
              "("
              (Term.hole "_")
              ":"
              [(«term_≠_»
                (Term.typeAscription "(" (num "0") ":" [(Term.app `Fin [(num "2")])] ")")
                "≠"
                (num "1"))]
              ")")])
           [])
          []
          (tactic__
           (cdotTk (patternIgnore (token.«· » "·")))
           [(Std.Tactic.Ext.«tacticExt___:_»
             "ext"
             [(Std.Tactic.RCases.rintroPat.one (Std.Tactic.RCases.rcasesPat.one `i))]
             [])
            []
            (Tactic.«tactic_<;>_»
             (Lean.Elab.Tactic.finCases "fin_cases" [`i] [])
             "<;>"
             (Tactic.tacticRfl "rfl"))])
          []
          (tactic__
           (cdotTk (patternIgnore (token.«· » "·")))
           [(Mathlib.Tactic.normNum "norm_num" [] [] [])])])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (tactic__
       (cdotTk (patternIgnore (token.«· » "·")))
       [(Mathlib.Tactic.normNum "norm_num" [] [] [])])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Mathlib.Tactic.normNum "norm_num" [] [] [])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (tactic__
       (cdotTk (patternIgnore (token.«· » "·")))
       [(Std.Tactic.Ext.«tacticExt___:_»
         "ext"
         [(Std.Tactic.RCases.rintroPat.one (Std.Tactic.RCases.rcasesPat.one `i))]
         [])
        []
        (Tactic.«tactic_<;>_»
         (Lean.Elab.Tactic.finCases "fin_cases" [`i] [])
         "<;>"
         (Tactic.tacticRfl "rfl"))])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.«tactic_<;>_»
       (Lean.Elab.Tactic.finCases "fin_cases" [`i] [])
       "<;>"
       (Tactic.tacticRfl "rfl"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.tacticRfl "rfl")
[PrettyPrinter.parenthesize] ...precedences are 2 >? 1024
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1, tactic))
      (Lean.Elab.Tactic.finCases "fin_cases" [`i] [])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'null', expected 'token.«*»'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `i
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Std.Tactic.Ext.«tacticExt___:_»
       "ext"
       [(Std.Tactic.RCases.rintroPat.one (Std.Tactic.RCases.rcasesPat.one `i))]
       [])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (convert
       "convert"
       []
       (Term.app
        `o.volume_form.map_swap
        [(Matrix.Data.Fin.VecNotation.«term![_,» "![" [`y "," `x] "]")
         (Term.typeAscription
          "("
          (Term.hole "_")
          ":"
          [(«term_≠_»
            (Term.typeAscription "(" (num "0") ":" [(Term.app `Fin [(num "2")])] ")")
            "≠"
            (num "1"))]
          ")")])
       [])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       `o.volume_form.map_swap
       [(Matrix.Data.Fin.VecNotation.«term![_,» "![" [`y "," `x] "]")
        (Term.typeAscription
         "("
         (Term.hole "_")
         ":"
         [(«term_≠_»
           (Term.typeAscription "(" (num "0") ":" [(Term.app `Fin [(num "2")])] ")")
           "≠"
           (num "1"))]
         ")")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.typeAscription', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.typeAscription', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.typeAscription
       "("
       (Term.hole "_")
       ":"
       [(«term_≠_»
         (Term.typeAscription "(" (num "0") ":" [(Term.app `Fin [(num "2")])] ")")
         "≠"
         (num "1"))]
       ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_≠_»
       (Term.typeAscription "(" (num "0") ":" [(Term.app `Fin [(num "2")])] ")")
       "≠"
       (num "1"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (num "1")
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 50, term))
      (Term.typeAscription "(" (num "0") ":" [(Term.app `Fin [(num "2")])] ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `Fin [(num "2")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'num', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'num', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (num "2")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `Fin
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (num "0")
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1024, (none, [anonymous]) <=? (some 50, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 50, (some 51, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Matrix.Data.Fin.VecNotation.«term![_,»', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Matrix.Data.Fin.VecNotation.«term![_,»', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, term))
      (Matrix.Data.Fin.VecNotation.«term![_,» "![" [`y "," `x] "]")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `x
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `y
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1023, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `o.volume_form.map_swap
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.simp
       "simp"
       []
       []
       ["only"]
       ["[" [(Tactic.simpLemma [] [] `area_form_to_volume_form)] "]"]
       [])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `area_form_to_volume_form
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, tactic) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
      («term_=_»
       (Term.app (Orientation.Analysis.InnerProductSpace.TwoDim.termω "ω") [`x `y])
       "="
       («term-_» "-" (Term.app (Orientation.Analysis.InnerProductSpace.TwoDim.termω "ω") [`y `x])))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term-_» "-" (Term.app (Orientation.Analysis.InnerProductSpace.TwoDim.termω "ω") [`y `x]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app (Orientation.Analysis.InnerProductSpace.TwoDim.termω "ω") [`y `x])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `x
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `y
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (Orientation.Analysis.InnerProductSpace.TwoDim.termω "ω")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Orientation.Analysis.InnerProductSpace.TwoDim.termω', expected 'Orientation.Analysis.InnerProductSpace.TwoDim.termω._@.Analysis.InnerProductSpace.TwoDim._hyg.7'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.opaque'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.instance'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.axiom'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.example'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.inductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.classInductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.structure'-/-- failed to format: format: uncaught backtrack exception
theorem
  area_form_swap
  ( x y : E ) : ω x y = - ω y x
  :=
    by
      simp only [ area_form_to_volume_form ]
        convert o.volume_form.map_swap ![ y , x ] ( _ : ( 0 : Fin 2 ) ≠ 1 )
        · ext i fin_cases i <;> rfl
        · norm_num
#align orientation.area_form_swap Orientation.area_form_swap

@[simp]
theorem area_form_neg_orientation : (-o).areaForm = -o.areaForm :=
  by
  ext (x y)
  simp [area_form_to_volume_form]
#align orientation.area_form_neg_orientation Orientation.area_form_neg_orientation

/-- Continuous linear map version of `orientation.area_form`, useful for calculus. -/
def areaForm' : E →L[ℝ] E →L[ℝ] ℝ :=
  (↑(LinearMap.toContinuousLinearMap : (E →ₗ[ℝ] ℝ) ≃ₗ[ℝ] E →L[ℝ] ℝ) ∘ₗ
      o.areaForm).toContinuousLinearMap
#align orientation.area_form' Orientation.areaForm'

@[simp]
theorem area_form'_apply (x : E) : o.areaForm' x = (o.areaForm x).toContinuousLinearMap :=
  rfl
#align orientation.area_form'_apply Orientation.area_form'_apply

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers [] [] [] [] [] [])
     (Command.theorem
      "theorem"
      (Command.declId `abs_area_form_le [])
      (Command.declSig
       [(Term.explicitBinder "(" [`x `y] [":" `E] [] ")")]
       (Term.typeSpec
        ":"
        («term_≤_»
         («term|___|»
          (group "|")
          (Term.app (Orientation.Analysis.InnerProductSpace.TwoDim.termω "ω") [`x `y])
          (group)
          "|")
         "≤"
         («term_*_»
          (Analysis.Normed.Group.Basic.«term‖_‖» "‖" `x "‖")
          "*"
          (Analysis.Normed.Group.Basic.«term‖_‖» "‖" `y "‖")))))
      (Command.declValSimple
       ":="
       (Term.byTactic
        "by"
        (Tactic.tacticSeq
         (Tactic.tacticSeq1Indented
          [(Std.Tactic.Simpa.simpa
            "simpa"
            []
            []
            (Std.Tactic.Simpa.simpaArgsRest
             []
             []
             []
             [(Tactic.simpArgs
               "["
               [(Tactic.simpLemma [] [] `area_form_to_volume_form)
                ","
                (Tactic.simpLemma [] [] `Fin.prod_univ_succ)]
               "]")]
             ["using"
              (Term.app
               `o.abs_volume_form_apply_le
               [(Matrix.Data.Fin.VecNotation.«term![_,» "![" [`x "," `y] "]")])]))])))
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
         [(Std.Tactic.Simpa.simpa
           "simpa"
           []
           []
           (Std.Tactic.Simpa.simpaArgsRest
            []
            []
            []
            [(Tactic.simpArgs
              "["
              [(Tactic.simpLemma [] [] `area_form_to_volume_form)
               ","
               (Tactic.simpLemma [] [] `Fin.prod_univ_succ)]
              "]")]
            ["using"
             (Term.app
              `o.abs_volume_form_apply_le
              [(Matrix.Data.Fin.VecNotation.«term![_,» "![" [`x "," `y] "]")])]))])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Std.Tactic.Simpa.simpa
       "simpa"
       []
       []
       (Std.Tactic.Simpa.simpaArgsRest
        []
        []
        []
        [(Tactic.simpArgs
          "["
          [(Tactic.simpLemma [] [] `area_form_to_volume_form)
           ","
           (Tactic.simpLemma [] [] `Fin.prod_univ_succ)]
          "]")]
        ["using"
         (Term.app
          `o.abs_volume_form_apply_le
          [(Matrix.Data.Fin.VecNotation.«term![_,» "![" [`x "," `y] "]")])]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       `o.abs_volume_form_apply_le
       [(Matrix.Data.Fin.VecNotation.«term![_,» "![" [`x "," `y] "]")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Matrix.Data.Fin.VecNotation.«term![_,»', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Matrix.Data.Fin.VecNotation.«term![_,»', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Matrix.Data.Fin.VecNotation.«term![_,» "![" [`x "," `y] "]")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `y
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `x
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `o.abs_volume_form_apply_le
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `Fin.prod_univ_succ
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `area_form_to_volume_form
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, tactic) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
      («term_≤_»
       («term|___|»
        (group "|")
        (Term.app (Orientation.Analysis.InnerProductSpace.TwoDim.termω "ω") [`x `y])
        (group)
        "|")
       "≤"
       («term_*_»
        (Analysis.Normed.Group.Basic.«term‖_‖» "‖" `x "‖")
        "*"
        (Analysis.Normed.Group.Basic.«term‖_‖» "‖" `y "‖")))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_*_»
       (Analysis.Normed.Group.Basic.«term‖_‖» "‖" `x "‖")
       "*"
       (Analysis.Normed.Group.Basic.«term‖_‖» "‖" `y "‖"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Analysis.Normed.Group.Basic.«term‖_‖» "‖" `y "‖")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `y
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 71 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 70, term))
      (Analysis.Normed.Group.Basic.«term‖_‖» "‖" `x "‖")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `x
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 70 >? 1024, (none, [anonymous]) <=? (some 70, term)
[PrettyPrinter.parenthesize] ...precedences are 51 >? 70, (some 71, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 50, term))
      («term|___|»
       (group "|")
       (Term.app (Orientation.Analysis.InnerProductSpace.TwoDim.termω "ω") [`x `y])
       (group)
       "|")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app (Orientation.Analysis.InnerProductSpace.TwoDim.termω "ω") [`x `y])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `y
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `x
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (Orientation.Analysis.InnerProductSpace.TwoDim.termω "ω")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Orientation.Analysis.InnerProductSpace.TwoDim.termω', expected 'Orientation.Analysis.InnerProductSpace.TwoDim.termω._@.Analysis.InnerProductSpace.TwoDim._hyg.7'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.opaque'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.instance'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.axiom'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.example'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.inductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.classInductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.structure'-/-- failed to format: format: uncaught backtrack exception
theorem
  abs_area_form_le
  ( x y : E ) : | ω x y | ≤ ‖ x ‖ * ‖ y ‖
  :=
    by
      simpa
        [ area_form_to_volume_form , Fin.prod_univ_succ ]
          using o.abs_volume_form_apply_le ![ x , y ]
#align orientation.abs_area_form_le Orientation.abs_area_form_le

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers [] [] [] [] [] [])
     (Command.theorem
      "theorem"
      (Command.declId `area_form_le [])
      (Command.declSig
       [(Term.explicitBinder "(" [`x `y] [":" `E] [] ")")]
       (Term.typeSpec
        ":"
        («term_≤_»
         (Term.app (Orientation.Analysis.InnerProductSpace.TwoDim.termω "ω") [`x `y])
         "≤"
         («term_*_»
          (Analysis.Normed.Group.Basic.«term‖_‖» "‖" `x "‖")
          "*"
          (Analysis.Normed.Group.Basic.«term‖_‖» "‖" `y "‖")))))
      (Command.declValSimple
       ":="
       (Term.byTactic
        "by"
        (Tactic.tacticSeq
         (Tactic.tacticSeq1Indented
          [(Std.Tactic.Simpa.simpa
            "simpa"
            []
            []
            (Std.Tactic.Simpa.simpaArgsRest
             []
             []
             []
             [(Tactic.simpArgs
               "["
               [(Tactic.simpLemma [] [] `area_form_to_volume_form)
                ","
                (Tactic.simpLemma [] [] `Fin.prod_univ_succ)]
               "]")]
             ["using"
              (Term.app
               `o.volume_form_apply_le
               [(Matrix.Data.Fin.VecNotation.«term![_,» "![" [`x "," `y] "]")])]))])))
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
         [(Std.Tactic.Simpa.simpa
           "simpa"
           []
           []
           (Std.Tactic.Simpa.simpaArgsRest
            []
            []
            []
            [(Tactic.simpArgs
              "["
              [(Tactic.simpLemma [] [] `area_form_to_volume_form)
               ","
               (Tactic.simpLemma [] [] `Fin.prod_univ_succ)]
              "]")]
            ["using"
             (Term.app
              `o.volume_form_apply_le
              [(Matrix.Data.Fin.VecNotation.«term![_,» "![" [`x "," `y] "]")])]))])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Std.Tactic.Simpa.simpa
       "simpa"
       []
       []
       (Std.Tactic.Simpa.simpaArgsRest
        []
        []
        []
        [(Tactic.simpArgs
          "["
          [(Tactic.simpLemma [] [] `area_form_to_volume_form)
           ","
           (Tactic.simpLemma [] [] `Fin.prod_univ_succ)]
          "]")]
        ["using"
         (Term.app
          `o.volume_form_apply_le
          [(Matrix.Data.Fin.VecNotation.«term![_,» "![" [`x "," `y] "]")])]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       `o.volume_form_apply_le
       [(Matrix.Data.Fin.VecNotation.«term![_,» "![" [`x "," `y] "]")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Matrix.Data.Fin.VecNotation.«term![_,»', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Matrix.Data.Fin.VecNotation.«term![_,»', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Matrix.Data.Fin.VecNotation.«term![_,» "![" [`x "," `y] "]")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `y
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `x
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `o.volume_form_apply_le
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `Fin.prod_univ_succ
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `area_form_to_volume_form
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, tactic) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
      («term_≤_»
       (Term.app (Orientation.Analysis.InnerProductSpace.TwoDim.termω "ω") [`x `y])
       "≤"
       («term_*_»
        (Analysis.Normed.Group.Basic.«term‖_‖» "‖" `x "‖")
        "*"
        (Analysis.Normed.Group.Basic.«term‖_‖» "‖" `y "‖")))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_*_»
       (Analysis.Normed.Group.Basic.«term‖_‖» "‖" `x "‖")
       "*"
       (Analysis.Normed.Group.Basic.«term‖_‖» "‖" `y "‖"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Analysis.Normed.Group.Basic.«term‖_‖» "‖" `y "‖")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `y
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 71 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 70, term))
      (Analysis.Normed.Group.Basic.«term‖_‖» "‖" `x "‖")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `x
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 70 >? 1024, (none, [anonymous]) <=? (some 70, term)
[PrettyPrinter.parenthesize] ...precedences are 51 >? 70, (some 71, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 50, term))
      (Term.app (Orientation.Analysis.InnerProductSpace.TwoDim.termω "ω") [`x `y])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `y
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `x
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (Orientation.Analysis.InnerProductSpace.TwoDim.termω "ω")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Orientation.Analysis.InnerProductSpace.TwoDim.termω', expected 'Orientation.Analysis.InnerProductSpace.TwoDim.termω._@.Analysis.InnerProductSpace.TwoDim._hyg.7'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.opaque'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.instance'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.axiom'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.example'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.inductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.classInductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.structure'-/-- failed to format: format: uncaught backtrack exception
theorem
  area_form_le
  ( x y : E ) : ω x y ≤ ‖ x ‖ * ‖ y ‖
  :=
    by
      simpa
        [ area_form_to_volume_form , Fin.prod_univ_succ ] using o.volume_form_apply_le ![ x , y ]
#align orientation.area_form_le Orientation.area_form_le

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers [] [] [] [] [] [])
     (Command.theorem
      "theorem"
      (Command.declId `abs_area_form_of_orthogonal [])
      (Command.declSig
       [(Term.implicitBinder "{" [`x `y] [":" `E] "}")
        (Term.explicitBinder
         "("
         [`h]
         [":"
          («term_=_»
           (RealInnerProductSpace.Analysis.InnerProductSpace.Basic.inner.real "⟪" `x ", " `y "⟫")
           "="
           (num "0"))]
         []
         ")")]
       (Term.typeSpec
        ":"
        («term_=_»
         («term|___|»
          (group "|")
          (Term.app (Orientation.Analysis.InnerProductSpace.TwoDim.termω "ω") [`x `y])
          (group)
          "|")
         "="
         («term_*_»
          (Analysis.Normed.Group.Basic.«term‖_‖» "‖" `x "‖")
          "*"
          (Analysis.Normed.Group.Basic.«term‖_‖» "‖" `y "‖")))))
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
             [(Tactic.rwRule [] `o.area_form_to_volume_form)
              ","
              (Tactic.rwRule [] `o.abs_volume_form_apply_of_pairwise_orthogonal)]
             "]")
            [])
           []
           (tactic__
            (cdotTk (patternIgnore (token.«· » "·")))
            [(Tactic.simp
              "simp"
              []
              []
              []
              ["[" [(Tactic.simpLemma [] [] `Fin.prod_univ_succ)] "]"]
              [])])
           []
           (Tactic.intro "intro" [`i `j `hij])
           []
           (Tactic.«tactic_<;>_»
            (Lean.Elab.Tactic.finCases "fin_cases" [`i] [])
            "<;>"
            (Lean.Elab.Tactic.finCases "fin_cases" [`j] []))
           []
           (tactic__
            (cdotTk (patternIgnore (token.«· » "·")))
            [(Std.Tactic.Simpa.simpa
              "simpa"
              []
              []
              (Std.Tactic.Simpa.simpaArgsRest [] [] [] [] []))])
           []
           (tactic__
            (cdotTk (patternIgnore (token.«· » "·")))
            [(Std.Tactic.Simpa.simpa
              "simpa"
              []
              []
              (Std.Tactic.Simpa.simpaArgsRest [] [] [] [] ["using" `h]))])
           []
           (tactic__
            (cdotTk (patternIgnore (token.«· » "·")))
            [(Std.Tactic.Simpa.simpa
              "simpa"
              []
              []
              (Std.Tactic.Simpa.simpaArgsRest
               []
               []
               []
               [(Tactic.simpArgs "[" [(Tactic.simpLemma [] [] `real_inner_comm)] "]")]
               ["using" `h]))])
           []
           (tactic__
            (cdotTk (patternIgnore (token.«· » "·")))
            [(Std.Tactic.Simpa.simpa
              "simpa"
              []
              []
              (Std.Tactic.Simpa.simpaArgsRest [] [] [] [] []))])])))
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
            [(Tactic.rwRule [] `o.area_form_to_volume_form)
             ","
             (Tactic.rwRule [] `o.abs_volume_form_apply_of_pairwise_orthogonal)]
            "]")
           [])
          []
          (tactic__
           (cdotTk (patternIgnore (token.«· » "·")))
           [(Tactic.simp
             "simp"
             []
             []
             []
             ["[" [(Tactic.simpLemma [] [] `Fin.prod_univ_succ)] "]"]
             [])])
          []
          (Tactic.intro "intro" [`i `j `hij])
          []
          (Tactic.«tactic_<;>_»
           (Lean.Elab.Tactic.finCases "fin_cases" [`i] [])
           "<;>"
           (Lean.Elab.Tactic.finCases "fin_cases" [`j] []))
          []
          (tactic__
           (cdotTk (patternIgnore (token.«· » "·")))
           [(Std.Tactic.Simpa.simpa "simpa" [] [] (Std.Tactic.Simpa.simpaArgsRest [] [] [] [] []))])
          []
          (tactic__
           (cdotTk (patternIgnore (token.«· » "·")))
           [(Std.Tactic.Simpa.simpa
             "simpa"
             []
             []
             (Std.Tactic.Simpa.simpaArgsRest [] [] [] [] ["using" `h]))])
          []
          (tactic__
           (cdotTk (patternIgnore (token.«· » "·")))
           [(Std.Tactic.Simpa.simpa
             "simpa"
             []
             []
             (Std.Tactic.Simpa.simpaArgsRest
              []
              []
              []
              [(Tactic.simpArgs "[" [(Tactic.simpLemma [] [] `real_inner_comm)] "]")]
              ["using" `h]))])
          []
          (tactic__
           (cdotTk (patternIgnore (token.«· » "·")))
           [(Std.Tactic.Simpa.simpa
             "simpa"
             []
             []
             (Std.Tactic.Simpa.simpaArgsRest [] [] [] [] []))])])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (tactic__
       (cdotTk (patternIgnore (token.«· » "·")))
       [(Std.Tactic.Simpa.simpa "simpa" [] [] (Std.Tactic.Simpa.simpaArgsRest [] [] [] [] []))])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Std.Tactic.Simpa.simpa "simpa" [] [] (Std.Tactic.Simpa.simpaArgsRest [] [] [] [] []))
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (tactic__
       (cdotTk (patternIgnore (token.«· » "·")))
       [(Std.Tactic.Simpa.simpa
         "simpa"
         []
         []
         (Std.Tactic.Simpa.simpaArgsRest
          []
          []
          []
          [(Tactic.simpArgs "[" [(Tactic.simpLemma [] [] `real_inner_comm)] "]")]
          ["using" `h]))])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Std.Tactic.Simpa.simpa
       "simpa"
       []
       []
       (Std.Tactic.Simpa.simpaArgsRest
        []
        []
        []
        [(Tactic.simpArgs "[" [(Tactic.simpLemma [] [] `real_inner_comm)] "]")]
        ["using" `h]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `h
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `real_inner_comm
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (tactic__
       (cdotTk (patternIgnore (token.«· » "·")))
       [(Std.Tactic.Simpa.simpa
         "simpa"
         []
         []
         (Std.Tactic.Simpa.simpaArgsRest [] [] [] [] ["using" `h]))])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Std.Tactic.Simpa.simpa
       "simpa"
       []
       []
       (Std.Tactic.Simpa.simpaArgsRest [] [] [] [] ["using" `h]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `h
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (tactic__
       (cdotTk (patternIgnore (token.«· » "·")))
       [(Std.Tactic.Simpa.simpa "simpa" [] [] (Std.Tactic.Simpa.simpaArgsRest [] [] [] [] []))])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Std.Tactic.Simpa.simpa "simpa" [] [] (Std.Tactic.Simpa.simpaArgsRest [] [] [] [] []))
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.«tactic_<;>_»
       (Lean.Elab.Tactic.finCases "fin_cases" [`i] [])
       "<;>"
       (Lean.Elab.Tactic.finCases "fin_cases" [`j] []))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Lean.Elab.Tactic.finCases "fin_cases" [`j] [])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'null', expected 'token.«*»'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `j
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 2 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1, tactic))
      (Lean.Elab.Tactic.finCases "fin_cases" [`i] [])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'null', expected 'token.«*»'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `i
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.intro "intro" [`i `j `hij])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `hij
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `j
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `i
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (tactic__
       (cdotTk (patternIgnore (token.«· » "·")))
       [(Tactic.simp "simp" [] [] [] ["[" [(Tactic.simpLemma [] [] `Fin.prod_univ_succ)] "]"] [])])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.simp "simp" [] [] [] ["[" [(Tactic.simpLemma [] [] `Fin.prod_univ_succ)] "]"] [])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `Fin.prod_univ_succ
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
        [(Tactic.rwRule [] `o.area_form_to_volume_form)
         ","
         (Tactic.rwRule [] `o.abs_volume_form_apply_of_pairwise_orthogonal)]
        "]")
       [])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `o.abs_volume_form_apply_of_pairwise_orthogonal
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `o.area_form_to_volume_form
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, tactic) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
      («term_=_»
       («term|___|»
        (group "|")
        (Term.app (Orientation.Analysis.InnerProductSpace.TwoDim.termω "ω") [`x `y])
        (group)
        "|")
       "="
       («term_*_»
        (Analysis.Normed.Group.Basic.«term‖_‖» "‖" `x "‖")
        "*"
        (Analysis.Normed.Group.Basic.«term‖_‖» "‖" `y "‖")))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_*_»
       (Analysis.Normed.Group.Basic.«term‖_‖» "‖" `x "‖")
       "*"
       (Analysis.Normed.Group.Basic.«term‖_‖» "‖" `y "‖"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Analysis.Normed.Group.Basic.«term‖_‖» "‖" `y "‖")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `y
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 71 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 70, term))
      (Analysis.Normed.Group.Basic.«term‖_‖» "‖" `x "‖")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `x
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 70 >? 1024, (none, [anonymous]) <=? (some 70, term)
[PrettyPrinter.parenthesize] ...precedences are 51 >? 70, (some 71, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 50, term))
      («term|___|»
       (group "|")
       (Term.app (Orientation.Analysis.InnerProductSpace.TwoDim.termω "ω") [`x `y])
       (group)
       "|")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app (Orientation.Analysis.InnerProductSpace.TwoDim.termω "ω") [`x `y])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `y
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `x
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (Orientation.Analysis.InnerProductSpace.TwoDim.termω "ω")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Orientation.Analysis.InnerProductSpace.TwoDim.termω', expected 'Orientation.Analysis.InnerProductSpace.TwoDim.termω._@.Analysis.InnerProductSpace.TwoDim._hyg.7'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.opaque'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.instance'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.axiom'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.example'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.inductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.classInductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.structure'-/-- failed to format: format: uncaught backtrack exception
theorem
  abs_area_form_of_orthogonal
  { x y : E } ( h : ⟪ x , y ⟫ = 0 ) : | ω x y | = ‖ x ‖ * ‖ y ‖
  :=
    by
      rw [ o.area_form_to_volume_form , o.abs_volume_form_apply_of_pairwise_orthogonal ]
        · simp [ Fin.prod_univ_succ ]
        intro i j hij
        fin_cases i <;> fin_cases j
        · simpa
        · simpa using h
        · simpa [ real_inner_comm ] using h
        · simpa
#align orientation.abs_area_form_of_orthogonal Orientation.abs_area_form_of_orthogonal

theorem area_form_map {F : Type _} [InnerProductSpace ℝ F] [Fact (finrank ℝ F = 2)] (φ : E ≃ₗᵢ[ℝ] F)
    (x y : F) :
    (Orientation.map (Fin 2) φ.toLinearEquiv o).areaForm x y = o.areaForm (φ.symm x) (φ.symm y) :=
  by
  have : φ.symm ∘ ![x, y] = ![φ.symm x, φ.symm y] :=
    by
    ext i
    fin_cases i <;> rfl
  simp [area_form_to_volume_form, volume_form_map, this]
#align orientation.area_form_map Orientation.area_form_map

/-- The area form is invariant under pullback by a positively-oriented isometric automorphism. -/
theorem area_form_comp_linear_isometry_equiv (φ : E ≃ₗᵢ[ℝ] E)
    (hφ : 0 < (φ.toLinearEquiv : E →ₗ[ℝ] E).det) (x y : E) :
    o.areaForm (φ x) (φ y) = o.areaForm x y :=
  by
  convert o.area_form_map φ (φ x) (φ y)
  · symm
    rwa [← o.map_eq_iff_det_pos φ.to_linear_equiv] at hφ
    rw [Fact.out (finrank ℝ E = 2), Fintype.card_fin]
  · simp
  · simp
#align
  orientation.area_form_comp_linear_isometry_equiv Orientation.area_form_comp_linear_isometry_equiv

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Lean.Elab.Command.command_Irreducible_def___
     (Command.declModifiers
      [(Command.docComment
        "/--"
        "Auxiliary construction for `orientation.right_angle_rotation`, rotation by 90 degrees in an\noriented real inner product space of dimension 2. -/")]
      []
      []
      []
      []
      [])
     "irreducible_def"
     (Command.declId `rightAngleRotationAux₁ [])
     (Command.optDeclSig
      []
      [(Term.typeSpec
        ":"
        (Algebra.Module.LinearMap.«term_→ₗ[_]_» `E " →ₗ[" (Data.Real.Basic.termℝ "ℝ") "] " `E))])
     (Command.declValSimple
      ":="
      (Term.let
       "let"
       (Term.letDecl
        (Term.letIdDecl
         `to_dual
         []
         [(Term.typeSpec
           ":"
           (Algebra.Module.Equiv.«term_≃ₗ[_]_»
            `E
            " ≃ₗ["
            (Data.Real.Basic.termℝ "ℝ")
            "] "
            (Algebra.Module.LinearMap.«term_→ₗ[_]_»
             `E
             " →ₗ["
             (Data.Real.Basic.termℝ "ℝ")
             "] "
             (Data.Real.Basic.termℝ "ℝ"))))]
         ":="
         (LinearEquiv.Algebra.Module.Equiv.«term_≪≫ₗ_»
          (Term.proj
           (Term.app `InnerProductSpace.toDual [(Data.Real.Basic.termℝ "ℝ") `E])
           "."
           `toLinearEquiv)
          " ≪≫ₗ "
          (Term.proj `LinearMap.toContinuousLinearMap "." `symm))))
       []
       (LinearMap.Algebra.Module.LinearMap.«term_∘ₗ_»
        (coeNotation "↑" (Term.proj `to_dual "." `symm))
        " ∘ₗ "
        (Orientation.Analysis.InnerProductSpace.TwoDim.termω "ω")))
      []))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.let
       "let"
       (Term.letDecl
        (Term.letIdDecl
         `to_dual
         []
         [(Term.typeSpec
           ":"
           (Algebra.Module.Equiv.«term_≃ₗ[_]_»
            `E
            " ≃ₗ["
            (Data.Real.Basic.termℝ "ℝ")
            "] "
            (Algebra.Module.LinearMap.«term_→ₗ[_]_»
             `E
             " →ₗ["
             (Data.Real.Basic.termℝ "ℝ")
             "] "
             (Data.Real.Basic.termℝ "ℝ"))))]
         ":="
         (LinearEquiv.Algebra.Module.Equiv.«term_≪≫ₗ_»
          (Term.proj
           (Term.app `InnerProductSpace.toDual [(Data.Real.Basic.termℝ "ℝ") `E])
           "."
           `toLinearEquiv)
          " ≪≫ₗ "
          (Term.proj `LinearMap.toContinuousLinearMap "." `symm))))
       []
       (LinearMap.Algebra.Module.LinearMap.«term_∘ₗ_»
        (coeNotation "↑" (Term.proj `to_dual "." `symm))
        " ∘ₗ "
        (Orientation.Analysis.InnerProductSpace.TwoDim.termω "ω")))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (LinearMap.Algebra.Module.LinearMap.«term_∘ₗ_»
       (coeNotation "↑" (Term.proj `to_dual "." `symm))
       " ∘ₗ "
       (Orientation.Analysis.InnerProductSpace.TwoDim.termω "ω"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Orientation.Analysis.InnerProductSpace.TwoDim.termω "ω")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Orientation.Analysis.InnerProductSpace.TwoDim.termω', expected 'Orientation.Analysis.InnerProductSpace.TwoDim.termω._@.Analysis.InnerProductSpace.TwoDim._hyg.7'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.declValSimple', expected 'Lean.Parser.Command.declValEqns'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.declValSimple', expected 'Lean.Parser.Command.whereStructInst'-/-- failed to format: format: uncaught backtrack exception
/--
    Auxiliary construction for `orientation.right_angle_rotation`, rotation by 90 degrees in an
    oriented real inner product space of dimension 2. -/
  irreducible_def
  rightAngleRotationAux₁
  : E →ₗ[ ℝ ] E
  :=
    let
      to_dual
        : E ≃ₗ[ ℝ ] E →ₗ[ ℝ ] ℝ
        :=
        InnerProductSpace.toDual ℝ E . toLinearEquiv ≪≫ₗ LinearMap.toContinuousLinearMap . symm
      ↑ to_dual . symm ∘ₗ ω
#align orientation.right_angle_rotation_aux₁ Orientation.rightAngleRotationAux₁

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers
      []
      [(Term.attributes "@[" [(Term.attrInstance (Term.attrKind []) (Attr.simp "simp" [] []))] "]")]
      []
      []
      []
      [])
     (Command.theorem
      "theorem"
      (Command.declId `inner_right_angle_rotation_aux₁_left [])
      (Command.declSig
       [(Term.explicitBinder "(" [`x `y] [":" `E] [] ")")]
       (Term.typeSpec
        ":"
        («term_=_»
         (RealInnerProductSpace.Analysis.InnerProductSpace.Basic.inner.real
          "⟪"
          (Term.app (Term.proj `o "." `rightAngleRotationAux₁) [`x])
          ", "
          `y
          "⟫")
         "="
         (Term.app (Orientation.Analysis.InnerProductSpace.TwoDim.termω "ω") [`x `y]))))
      (Command.declValSimple
       ":="
       (Term.byTactic
        "by"
        (Tactic.tacticSeq
         (Tactic.tacticSeq1Indented
          [(Tactic.simp
            "simp"
            []
            []
            ["only"]
            ["["
             [(Tactic.simpLemma [] [] `right_angle_rotation_aux₁)
              ","
              (Tactic.simpLemma [] [] `LinearEquiv.trans_symm)
              ","
              (Tactic.simpLemma [] [] `LinearEquiv.coe_trans)
              ","
              (Tactic.simpLemma [] [] `LinearEquiv.coe_coe)
              ","
              (Tactic.simpLemma [] [] `InnerProductSpace.to_dual_symm_apply)
              ","
              (Tactic.simpLemma [] [] `eq_self_iff_true)
              ","
              (Tactic.simpLemma [] [] `LinearMap.coe_to_continuous_linear_map')
              ","
              (Tactic.simpLemma [] [] `LinearIsometryEquiv.coe_to_linear_equiv)
              ","
              (Tactic.simpLemma [] [] `LinearMap.comp_apply)
              ","
              (Tactic.simpLemma [] [] `LinearEquiv.symm_symm)
              ","
              (Tactic.simpLemma [] [] `LinearIsometryEquiv.to_linear_equiv_symm)]
             "]"]
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
         [(Tactic.simp
           "simp"
           []
           []
           ["only"]
           ["["
            [(Tactic.simpLemma [] [] `right_angle_rotation_aux₁)
             ","
             (Tactic.simpLemma [] [] `LinearEquiv.trans_symm)
             ","
             (Tactic.simpLemma [] [] `LinearEquiv.coe_trans)
             ","
             (Tactic.simpLemma [] [] `LinearEquiv.coe_coe)
             ","
             (Tactic.simpLemma [] [] `InnerProductSpace.to_dual_symm_apply)
             ","
             (Tactic.simpLemma [] [] `eq_self_iff_true)
             ","
             (Tactic.simpLemma [] [] `LinearMap.coe_to_continuous_linear_map')
             ","
             (Tactic.simpLemma [] [] `LinearIsometryEquiv.coe_to_linear_equiv)
             ","
             (Tactic.simpLemma [] [] `LinearMap.comp_apply)
             ","
             (Tactic.simpLemma [] [] `LinearEquiv.symm_symm)
             ","
             (Tactic.simpLemma [] [] `LinearIsometryEquiv.to_linear_equiv_symm)]
            "]"]
           [])])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.simp
       "simp"
       []
       []
       ["only"]
       ["["
        [(Tactic.simpLemma [] [] `right_angle_rotation_aux₁)
         ","
         (Tactic.simpLemma [] [] `LinearEquiv.trans_symm)
         ","
         (Tactic.simpLemma [] [] `LinearEquiv.coe_trans)
         ","
         (Tactic.simpLemma [] [] `LinearEquiv.coe_coe)
         ","
         (Tactic.simpLemma [] [] `InnerProductSpace.to_dual_symm_apply)
         ","
         (Tactic.simpLemma [] [] `eq_self_iff_true)
         ","
         (Tactic.simpLemma [] [] `LinearMap.coe_to_continuous_linear_map')
         ","
         (Tactic.simpLemma [] [] `LinearIsometryEquiv.coe_to_linear_equiv)
         ","
         (Tactic.simpLemma [] [] `LinearMap.comp_apply)
         ","
         (Tactic.simpLemma [] [] `LinearEquiv.symm_symm)
         ","
         (Tactic.simpLemma [] [] `LinearIsometryEquiv.to_linear_equiv_symm)]
        "]"]
       [])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `LinearIsometryEquiv.to_linear_equiv_symm
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `LinearEquiv.symm_symm
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `LinearMap.comp_apply
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `LinearIsometryEquiv.coe_to_linear_equiv
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `LinearMap.coe_to_continuous_linear_map'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `eq_self_iff_true
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `InnerProductSpace.to_dual_symm_apply
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `LinearEquiv.coe_coe
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `LinearEquiv.coe_trans
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `LinearEquiv.trans_symm
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `right_angle_rotation_aux₁
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, tactic) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
      («term_=_»
       (RealInnerProductSpace.Analysis.InnerProductSpace.Basic.inner.real
        "⟪"
        (Term.app (Term.proj `o "." `rightAngleRotationAux₁) [`x])
        ", "
        `y
        "⟫")
       "="
       (Term.app (Orientation.Analysis.InnerProductSpace.TwoDim.termω "ω") [`x `y]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app (Orientation.Analysis.InnerProductSpace.TwoDim.termω "ω") [`x `y])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `y
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `x
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (Orientation.Analysis.InnerProductSpace.TwoDim.termω "ω")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Orientation.Analysis.InnerProductSpace.TwoDim.termω', expected 'Orientation.Analysis.InnerProductSpace.TwoDim.termω._@.Analysis.InnerProductSpace.TwoDim._hyg.7'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.opaque'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.instance'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.axiom'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.example'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.inductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.classInductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.structure'-/-- failed to format: format: uncaught backtrack exception
@[ simp ]
  theorem
    inner_right_angle_rotation_aux₁_left
    ( x y : E ) : ⟪ o . rightAngleRotationAux₁ x , y ⟫ = ω x y
    :=
      by
        simp
          only
          [
            right_angle_rotation_aux₁
              ,
              LinearEquiv.trans_symm
              ,
              LinearEquiv.coe_trans
              ,
              LinearEquiv.coe_coe
              ,
              InnerProductSpace.to_dual_symm_apply
              ,
              eq_self_iff_true
              ,
              LinearMap.coe_to_continuous_linear_map'
              ,
              LinearIsometryEquiv.coe_to_linear_equiv
              ,
              LinearMap.comp_apply
              ,
              LinearEquiv.symm_symm
              ,
              LinearIsometryEquiv.to_linear_equiv_symm
            ]
#align
  orientation.inner_right_angle_rotation_aux₁_left Orientation.inner_right_angle_rotation_aux₁_left

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers
      []
      [(Term.attributes "@[" [(Term.attrInstance (Term.attrKind []) (Attr.simp "simp" [] []))] "]")]
      []
      []
      []
      [])
     (Command.theorem
      "theorem"
      (Command.declId `inner_right_angle_rotation_aux₁_right [])
      (Command.declSig
       [(Term.explicitBinder "(" [`x `y] [":" `E] [] ")")]
       (Term.typeSpec
        ":"
        («term_=_»
         (RealInnerProductSpace.Analysis.InnerProductSpace.Basic.inner.real
          "⟪"
          `x
          ", "
          (Term.app (Term.proj `o "." `rightAngleRotationAux₁) [`y])
          "⟫")
         "="
         («term-_»
          "-"
          (Term.app (Orientation.Analysis.InnerProductSpace.TwoDim.termω "ω") [`x `y])))))
      (Command.declValSimple
       ":="
       (Term.byTactic
        "by"
        (Tactic.tacticSeq
         (Tactic.tacticSeq1Indented
          [(Tactic.rwSeq
            "rw"
            []
            (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `real_inner_comm)] "]")
            [])
           []
           (Tactic.simp
            "simp"
            []
            []
            []
            ["[" [(Tactic.simpLemma [] [] (Term.app `o.area_form_swap [`y `x]))] "]"]
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
         [(Tactic.rwSeq "rw" [] (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `real_inner_comm)] "]") [])
          []
          (Tactic.simp
           "simp"
           []
           []
           []
           ["[" [(Tactic.simpLemma [] [] (Term.app `o.area_form_swap [`y `x]))] "]"]
           [])])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.simp
       "simp"
       []
       []
       []
       ["[" [(Tactic.simpLemma [] [] (Term.app `o.area_form_swap [`y `x]))] "]"]
       [])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `o.area_form_swap [`y `x])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `x
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `y
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `o.area_form_swap
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.rwSeq "rw" [] (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `real_inner_comm)] "]") [])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `real_inner_comm
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, tactic) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
      («term_=_»
       (RealInnerProductSpace.Analysis.InnerProductSpace.Basic.inner.real
        "⟪"
        `x
        ", "
        (Term.app (Term.proj `o "." `rightAngleRotationAux₁) [`y])
        "⟫")
       "="
       («term-_» "-" (Term.app (Orientation.Analysis.InnerProductSpace.TwoDim.termω "ω") [`x `y])))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term-_» "-" (Term.app (Orientation.Analysis.InnerProductSpace.TwoDim.termω "ω") [`x `y]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app (Orientation.Analysis.InnerProductSpace.TwoDim.termω "ω") [`x `y])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `y
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `x
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (Orientation.Analysis.InnerProductSpace.TwoDim.termω "ω")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Orientation.Analysis.InnerProductSpace.TwoDim.termω', expected 'Orientation.Analysis.InnerProductSpace.TwoDim.termω._@.Analysis.InnerProductSpace.TwoDim._hyg.7'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.opaque'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.instance'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.axiom'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.example'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.inductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.classInductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.structure'-/-- failed to format: format: uncaught backtrack exception
@[ simp ]
  theorem
    inner_right_angle_rotation_aux₁_right
    ( x y : E ) : ⟪ x , o . rightAngleRotationAux₁ y ⟫ = - ω x y
    := by rw [ real_inner_comm ] simp [ o.area_form_swap y x ]
#align
  orientation.inner_right_angle_rotation_aux₁_right Orientation.inner_right_angle_rotation_aux₁_right

/-- Auxiliary construction for `orientation.right_angle_rotation`, rotation by 90 degrees in an
oriented real inner product space of dimension 2. -/
def rightAngleRotationAux₂ : E →ₗᵢ[ℝ] E :=
  { o.rightAngleRotationAux₁ with
    norm_map' := fun x => by
      dsimp
      refine' le_antisymm _ _
      · cases' eq_or_lt_of_le (norm_nonneg (o.right_angle_rotation_aux₁ x)) with h h
        · rw [← h]
          positivity
        refine' le_of_mul_le_mul_right _ h
        rw [← real_inner_self_eq_norm_mul_norm, o.inner_right_angle_rotation_aux₁_left]
        exact o.area_form_le x (o.right_angle_rotation_aux₁ x)
      · let K : Submodule ℝ E := ℝ ∙ x
        have : Nontrivial Kᗮ :=
          by
          apply @FiniteDimensional.nontrivial_of_finrank_pos ℝ
          have : finrank ℝ K ≤ Finset.card {x} :=
            by
            rw [← Set.to_finset_singleton]
            exact finrank_span_le_card ({x} : Set E)
          have : Finset.card {x} = 1 := Finset.card_singleton x
          have : finrank ℝ K + finrank ℝ Kᗮ = finrank ℝ E := K.finrank_add_finrank_orthogonal
          have : finrank ℝ E = 2 := Fact.out _
          linarith
        obtain ⟨w, hw₀⟩ : ∃ w : Kᗮ, w ≠ 0 := exists_ne 0
        have hw' : ⟪x, (w : E)⟫ = 0 := submodule.mem_orthogonal_singleton_iff_inner_right.mp w.2
        have hw : (w : E) ≠ 0 := fun h => hw₀ (submodule.coe_eq_zero.mp h)
        refine' le_of_mul_le_mul_right _ (by rwa [norm_pos_iff] : 0 < ‖(w : E)‖)
        rw [← o.abs_area_form_of_orthogonal hw']
        rw [← o.inner_right_angle_rotation_aux₁_left x w]
        exact abs_real_inner_le_norm (o.right_angle_rotation_aux₁ x) w }
#align orientation.right_angle_rotation_aux₂ Orientation.rightAngleRotationAux₂

@[simp]
theorem right_angle_rotation_aux₁_right_angle_rotation_aux₁ (x : E) :
    o.rightAngleRotationAux₁ (o.rightAngleRotationAux₁ x) = -x :=
  by
  apply ext_inner_left ℝ
  intro y
  have : ⟪o.right_angle_rotation_aux₁ y, o.right_angle_rotation_aux₁ x⟫ = ⟪y, x⟫ :=
    LinearIsometry.inner_map_map o.right_angle_rotation_aux₂ y x
  rw [o.inner_right_angle_rotation_aux₁_right, ← o.inner_right_angle_rotation_aux₁_left, this,
    inner_neg_right]
#align
  orientation.right_angle_rotation_aux₁_right_angle_rotation_aux₁ Orientation.right_angle_rotation_aux₁_right_angle_rotation_aux₁

/-- An isometric automorphism of an oriented real inner product space of dimension 2 (usual notation
`J`). This automorphism squares to -1.  We will define rotations in such a way that this
automorphism is equal to rotation by 90 degrees. -/
irreducible_def rightAngleRotation : E ≃ₗᵢ[ℝ] E :=
  LinearIsometryEquiv.ofLinearIsometry o.rightAngleRotationAux₂ (-o.rightAngleRotationAux₁)
    (by ext <;> simp [right_angle_rotation_aux₂]) (by ext <;> simp [right_angle_rotation_aux₂])
#align orientation.right_angle_rotation Orientation.rightAngleRotation

-- mathport name: exprJ
local notation "J" => o.rightAngleRotation

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers
      []
      [(Term.attributes "@[" [(Term.attrInstance (Term.attrKind []) (Attr.simp "simp" [] []))] "]")]
      []
      []
      []
      [])
     (Command.theorem
      "theorem"
      (Command.declId `inner_right_angle_rotation_left [])
      (Command.declSig
       [(Term.explicitBinder "(" [`x `y] [":" `E] [] ")")]
       (Term.typeSpec
        ":"
        («term_=_»
         (RealInnerProductSpace.Analysis.InnerProductSpace.Basic.inner.real
          "⟪"
          (Term.app (Orientation.Analysis.InnerProductSpace.TwoDim.termJ "J") [`x])
          ", "
          `y
          "⟫")
         "="
         (Term.app (Orientation.Analysis.InnerProductSpace.TwoDim.termω "ω") [`x `y]))))
      (Command.declValSimple
       ":="
       (Term.byTactic
        "by"
        (Tactic.tacticSeq
         (Tactic.tacticSeq1Indented
          [(Tactic.rwSeq
            "rw"
            []
            (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `right_angle_rotation)] "]")
            [])
           []
           (Tactic.exact "exact" (Term.app `o.inner_right_angle_rotation_aux₁_left [`x `y]))])))
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
           (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `right_angle_rotation)] "]")
           [])
          []
          (Tactic.exact "exact" (Term.app `o.inner_right_angle_rotation_aux₁_left [`x `y]))])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.exact "exact" (Term.app `o.inner_right_angle_rotation_aux₁_left [`x `y]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `o.inner_right_angle_rotation_aux₁_left [`x `y])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `y
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `x
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `o.inner_right_angle_rotation_aux₁_left
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.rwSeq
       "rw"
       []
       (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `right_angle_rotation)] "]")
       [])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `right_angle_rotation
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, tactic) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
      («term_=_»
       (RealInnerProductSpace.Analysis.InnerProductSpace.Basic.inner.real
        "⟪"
        (Term.app (Orientation.Analysis.InnerProductSpace.TwoDim.termJ "J") [`x])
        ", "
        `y
        "⟫")
       "="
       (Term.app (Orientation.Analysis.InnerProductSpace.TwoDim.termω "ω") [`x `y]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app (Orientation.Analysis.InnerProductSpace.TwoDim.termω "ω") [`x `y])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `y
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `x
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (Orientation.Analysis.InnerProductSpace.TwoDim.termω "ω")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Orientation.Analysis.InnerProductSpace.TwoDim.termω', expected 'Orientation.Analysis.InnerProductSpace.TwoDim.termω._@.Analysis.InnerProductSpace.TwoDim._hyg.7'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.opaque'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.instance'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.axiom'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.example'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.inductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.classInductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.structure'-/-- failed to format: format: uncaught backtrack exception
@[ simp ]
  theorem
    inner_right_angle_rotation_left
    ( x y : E ) : ⟪ J x , y ⟫ = ω x y
    := by rw [ right_angle_rotation ] exact o.inner_right_angle_rotation_aux₁_left x y
#align orientation.inner_right_angle_rotation_left Orientation.inner_right_angle_rotation_left

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers
      []
      [(Term.attributes "@[" [(Term.attrInstance (Term.attrKind []) (Attr.simp "simp" [] []))] "]")]
      []
      []
      []
      [])
     (Command.theorem
      "theorem"
      (Command.declId `inner_right_angle_rotation_right [])
      (Command.declSig
       [(Term.explicitBinder "(" [`x `y] [":" `E] [] ")")]
       (Term.typeSpec
        ":"
        («term_=_»
         (RealInnerProductSpace.Analysis.InnerProductSpace.Basic.inner.real
          "⟪"
          `x
          ", "
          (Term.app (Orientation.Analysis.InnerProductSpace.TwoDim.termJ "J") [`y])
          "⟫")
         "="
         («term-_»
          "-"
          (Term.app (Orientation.Analysis.InnerProductSpace.TwoDim.termω "ω") [`x `y])))))
      (Command.declValSimple
       ":="
       (Term.byTactic
        "by"
        (Tactic.tacticSeq
         (Tactic.tacticSeq1Indented
          [(Tactic.rwSeq
            "rw"
            []
            (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `right_angle_rotation)] "]")
            [])
           []
           (Tactic.exact "exact" (Term.app `o.inner_right_angle_rotation_aux₁_right [`x `y]))])))
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
           (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `right_angle_rotation)] "]")
           [])
          []
          (Tactic.exact "exact" (Term.app `o.inner_right_angle_rotation_aux₁_right [`x `y]))])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.exact "exact" (Term.app `o.inner_right_angle_rotation_aux₁_right [`x `y]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `o.inner_right_angle_rotation_aux₁_right [`x `y])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `y
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `x
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `o.inner_right_angle_rotation_aux₁_right
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.rwSeq
       "rw"
       []
       (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `right_angle_rotation)] "]")
       [])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `right_angle_rotation
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, tactic) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
      («term_=_»
       (RealInnerProductSpace.Analysis.InnerProductSpace.Basic.inner.real
        "⟪"
        `x
        ", "
        (Term.app (Orientation.Analysis.InnerProductSpace.TwoDim.termJ "J") [`y])
        "⟫")
       "="
       («term-_» "-" (Term.app (Orientation.Analysis.InnerProductSpace.TwoDim.termω "ω") [`x `y])))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term-_» "-" (Term.app (Orientation.Analysis.InnerProductSpace.TwoDim.termω "ω") [`x `y]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app (Orientation.Analysis.InnerProductSpace.TwoDim.termω "ω") [`x `y])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `y
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `x
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (Orientation.Analysis.InnerProductSpace.TwoDim.termω "ω")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Orientation.Analysis.InnerProductSpace.TwoDim.termω', expected 'Orientation.Analysis.InnerProductSpace.TwoDim.termω._@.Analysis.InnerProductSpace.TwoDim._hyg.7'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.opaque'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.instance'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.axiom'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.example'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.inductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.classInductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.structure'-/-- failed to format: format: uncaught backtrack exception
@[ simp ]
  theorem
    inner_right_angle_rotation_right
    ( x y : E ) : ⟪ x , J y ⟫ = - ω x y
    := by rw [ right_angle_rotation ] exact o.inner_right_angle_rotation_aux₁_right x y
#align orientation.inner_right_angle_rotation_right Orientation.inner_right_angle_rotation_right

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers
      []
      [(Term.attributes "@[" [(Term.attrInstance (Term.attrKind []) (Attr.simp "simp" [] []))] "]")]
      []
      []
      []
      [])
     (Command.theorem
      "theorem"
      (Command.declId `right_angle_rotation_right_angle_rotation [])
      (Command.declSig
       [(Term.explicitBinder "(" [`x] [":" `E] [] ")")]
       (Term.typeSpec
        ":"
        («term_=_»
         (Term.app
          (Orientation.Analysis.InnerProductSpace.TwoDim.termJ "J")
          [(Term.app (Orientation.Analysis.InnerProductSpace.TwoDim.termJ "J") [`x])])
         "="
         («term-_» "-" `x))))
      (Command.declValSimple
       ":="
       (Term.byTactic
        "by"
        (Tactic.tacticSeq
         (Tactic.tacticSeq1Indented
          [(Tactic.rwSeq
            "rw"
            []
            (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `right_angle_rotation)] "]")
            [])
           []
           (Tactic.exact
            "exact"
            (Term.app `o.right_angle_rotation_aux₁_right_angle_rotation_aux₁ [`x]))])))
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
           (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `right_angle_rotation)] "]")
           [])
          []
          (Tactic.exact
           "exact"
           (Term.app `o.right_angle_rotation_aux₁_right_angle_rotation_aux₁ [`x]))])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.exact "exact" (Term.app `o.right_angle_rotation_aux₁_right_angle_rotation_aux₁ [`x]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `o.right_angle_rotation_aux₁_right_angle_rotation_aux₁ [`x])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `x
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `o.right_angle_rotation_aux₁_right_angle_rotation_aux₁
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.rwSeq
       "rw"
       []
       (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `right_angle_rotation)] "]")
       [])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `right_angle_rotation
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, tactic) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
      («term_=_»
       (Term.app
        (Orientation.Analysis.InnerProductSpace.TwoDim.termJ "J")
        [(Term.app (Orientation.Analysis.InnerProductSpace.TwoDim.termJ "J") [`x])])
       "="
       («term-_» "-" `x))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term-_» "-" `x)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `x
[PrettyPrinter.parenthesize] ...precedences are 75 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 51 >? 75, (some 75, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 50, term))
      (Term.app
       (Orientation.Analysis.InnerProductSpace.TwoDim.termJ "J")
       [(Term.app (Orientation.Analysis.InnerProductSpace.TwoDim.termJ "J") [`x])])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app (Orientation.Analysis.InnerProductSpace.TwoDim.termJ "J") [`x])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `x
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (Orientation.Analysis.InnerProductSpace.TwoDim.termJ "J")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Orientation.Analysis.InnerProductSpace.TwoDim.termJ', expected 'Orientation.Analysis.InnerProductSpace.TwoDim.termJ._@.Analysis.InnerProductSpace.TwoDim._hyg.50'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.opaque'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.instance'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.axiom'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.example'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.inductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.classInductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.structure'-/-- failed to format: format: uncaught backtrack exception
@[ simp ]
  theorem
    right_angle_rotation_right_angle_rotation
    ( x : E ) : J J x = - x
    := by rw [ right_angle_rotation ] exact o.right_angle_rotation_aux₁_right_angle_rotation_aux₁ x
#align
  orientation.right_angle_rotation_right_angle_rotation Orientation.right_angle_rotation_right_angle_rotation

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers
      []
      [(Term.attributes "@[" [(Term.attrInstance (Term.attrKind []) (Attr.simp "simp" [] []))] "]")]
      []
      []
      []
      [])
     (Command.theorem
      "theorem"
      (Command.declId `right_angle_rotation_symm [])
      (Command.declSig
       []
       (Term.typeSpec
        ":"
        («term_=_»
         (Term.app
          `LinearIsometryEquiv.symm
          [(Orientation.Analysis.InnerProductSpace.TwoDim.termJ "J")])
         "="
         (Term.app
          `LinearIsometryEquiv.trans
          [(Orientation.Analysis.InnerProductSpace.TwoDim.termJ "J")
           (Term.app `LinearIsometryEquiv.neg [(Data.Real.Basic.termℝ "ℝ")])]))))
      (Command.declValSimple
       ":="
       (Term.byTactic
        "by"
        (Tactic.tacticSeq
         (Tactic.tacticSeq1Indented
          [(Tactic.rwSeq
            "rw"
            []
            (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `right_angle_rotation)] "]")
            [])
           []
           (Tactic.exact
            "exact"
            (Term.app `LinearIsometryEquiv.to_linear_isometry_injective [`rfl]))])))
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
           (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `right_angle_rotation)] "]")
           [])
          []
          (Tactic.exact
           "exact"
           (Term.app `LinearIsometryEquiv.to_linear_isometry_injective [`rfl]))])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.exact "exact" (Term.app `LinearIsometryEquiv.to_linear_isometry_injective [`rfl]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `LinearIsometryEquiv.to_linear_isometry_injective [`rfl])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `rfl
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `LinearIsometryEquiv.to_linear_isometry_injective
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.rwSeq
       "rw"
       []
       (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `right_angle_rotation)] "]")
       [])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `right_angle_rotation
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, tactic) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
      («term_=_»
       (Term.app
        `LinearIsometryEquiv.symm
        [(Orientation.Analysis.InnerProductSpace.TwoDim.termJ "J")])
       "="
       (Term.app
        `LinearIsometryEquiv.trans
        [(Orientation.Analysis.InnerProductSpace.TwoDim.termJ "J")
         (Term.app `LinearIsometryEquiv.neg [(Data.Real.Basic.termℝ "ℝ")])]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       `LinearIsometryEquiv.trans
       [(Orientation.Analysis.InnerProductSpace.TwoDim.termJ "J")
        (Term.app `LinearIsometryEquiv.neg [(Data.Real.Basic.termℝ "ℝ")])])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `LinearIsometryEquiv.neg [(Data.Real.Basic.termℝ "ℝ")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Data.Real.Basic.termℝ', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Data.Real.Basic.termℝ', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Data.Real.Basic.termℝ "ℝ")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `LinearIsometryEquiv.neg
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.app `LinearIsometryEquiv.neg [(Data.Real.Basic.termℝ "ℝ")])
     ")")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Orientation.Analysis.InnerProductSpace.TwoDim.termJ', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Orientation.Analysis.InnerProductSpace.TwoDim.termJ', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Orientation.Analysis.InnerProductSpace.TwoDim.termJ "J")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Orientation.Analysis.InnerProductSpace.TwoDim.termJ', expected 'Orientation.Analysis.InnerProductSpace.TwoDim.termJ._@.Analysis.InnerProductSpace.TwoDim._hyg.50'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.opaque'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.instance'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.axiom'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.example'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.inductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.classInductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.structure'-/-- failed to format: format: uncaught backtrack exception
@[ simp ]
  theorem
    right_angle_rotation_symm
    : LinearIsometryEquiv.symm J = LinearIsometryEquiv.trans J LinearIsometryEquiv.neg ℝ
    := by rw [ right_angle_rotation ] exact LinearIsometryEquiv.to_linear_isometry_injective rfl
#align orientation.right_angle_rotation_symm Orientation.right_angle_rotation_symm

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers
      []
      [(Term.attributes "@[" [(Term.attrInstance (Term.attrKind []) (Attr.simp "simp" [] []))] "]")]
      []
      []
      []
      [])
     (Command.theorem
      "theorem"
      (Command.declId `inner_right_angle_rotation_self [])
      (Command.declSig
       [(Term.explicitBinder "(" [`x] [":" `E] [] ")")]
       (Term.typeSpec
        ":"
        («term_=_»
         (RealInnerProductSpace.Analysis.InnerProductSpace.Basic.inner.real
          "⟪"
          (Term.app (Orientation.Analysis.InnerProductSpace.TwoDim.termJ "J") [`x])
          ", "
          `x
          "⟫")
         "="
         (num "0"))))
      (Command.declValSimple
       ":="
       (Term.byTactic
        "by"
        (Tactic.tacticSeq (Tactic.tacticSeq1Indented [(Tactic.simp "simp" [] [] [] [] [])])))
       [])
      []
      []))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.abbrev'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.def'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.byTactic
       "by"
       (Tactic.tacticSeq (Tactic.tacticSeq1Indented [(Tactic.simp "simp" [] [] [] [] [])])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.simp "simp" [] [] [] [] [])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, tactic) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
      («term_=_»
       (RealInnerProductSpace.Analysis.InnerProductSpace.Basic.inner.real
        "⟪"
        (Term.app (Orientation.Analysis.InnerProductSpace.TwoDim.termJ "J") [`x])
        ", "
        `x
        "⟫")
       "="
       (num "0"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (num "0")
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 50, term))
      (RealInnerProductSpace.Analysis.InnerProductSpace.Basic.inner.real
       "⟪"
       (Term.app (Orientation.Analysis.InnerProductSpace.TwoDim.termJ "J") [`x])
       ", "
       `x
       "⟫")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `x
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app (Orientation.Analysis.InnerProductSpace.TwoDim.termJ "J") [`x])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `x
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (Orientation.Analysis.InnerProductSpace.TwoDim.termJ "J")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Orientation.Analysis.InnerProductSpace.TwoDim.termJ', expected 'Orientation.Analysis.InnerProductSpace.TwoDim.termJ._@.Analysis.InnerProductSpace.TwoDim._hyg.50'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.opaque'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.instance'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.axiom'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.example'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.inductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.classInductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.structure'-/-- failed to format: format: uncaught backtrack exception
@[ simp ] theorem inner_right_angle_rotation_self ( x : E ) : ⟪ J x , x ⟫ = 0 := by simp
#align orientation.inner_right_angle_rotation_self Orientation.inner_right_angle_rotation_self

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers [] [] [] [] [] [])
     (Command.theorem
      "theorem"
      (Command.declId `inner_right_angle_rotation_swap [])
      (Command.declSig
       [(Term.explicitBinder "(" [`x `y] [":" `E] [] ")")]
       (Term.typeSpec
        ":"
        («term_=_»
         (RealInnerProductSpace.Analysis.InnerProductSpace.Basic.inner.real
          "⟪"
          `x
          ", "
          (Term.app (Orientation.Analysis.InnerProductSpace.TwoDim.termJ "J") [`y])
          "⟫")
         "="
         («term-_»
          "-"
          (RealInnerProductSpace.Analysis.InnerProductSpace.Basic.inner.real
           "⟪"
           (Term.app (Orientation.Analysis.InnerProductSpace.TwoDim.termJ "J") [`x])
           ", "
           `y
           "⟫")))))
      (Command.declValSimple
       ":="
       (Term.byTactic
        "by"
        (Tactic.tacticSeq (Tactic.tacticSeq1Indented [(Tactic.simp "simp" [] [] [] [] [])])))
       [])
      []
      []))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.abbrev'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.def'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.byTactic
       "by"
       (Tactic.tacticSeq (Tactic.tacticSeq1Indented [(Tactic.simp "simp" [] [] [] [] [])])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.simp "simp" [] [] [] [] [])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, tactic) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
      («term_=_»
       (RealInnerProductSpace.Analysis.InnerProductSpace.Basic.inner.real
        "⟪"
        `x
        ", "
        (Term.app (Orientation.Analysis.InnerProductSpace.TwoDim.termJ "J") [`y])
        "⟫")
       "="
       («term-_»
        "-"
        (RealInnerProductSpace.Analysis.InnerProductSpace.Basic.inner.real
         "⟪"
         (Term.app (Orientation.Analysis.InnerProductSpace.TwoDim.termJ "J") [`x])
         ", "
         `y
         "⟫")))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term-_»
       "-"
       (RealInnerProductSpace.Analysis.InnerProductSpace.Basic.inner.real
        "⟪"
        (Term.app (Orientation.Analysis.InnerProductSpace.TwoDim.termJ "J") [`x])
        ", "
        `y
        "⟫"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (RealInnerProductSpace.Analysis.InnerProductSpace.Basic.inner.real
       "⟪"
       (Term.app (Orientation.Analysis.InnerProductSpace.TwoDim.termJ "J") [`x])
       ", "
       `y
       "⟫")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `y
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app (Orientation.Analysis.InnerProductSpace.TwoDim.termJ "J") [`x])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `x
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (Orientation.Analysis.InnerProductSpace.TwoDim.termJ "J")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Orientation.Analysis.InnerProductSpace.TwoDim.termJ', expected 'Orientation.Analysis.InnerProductSpace.TwoDim.termJ._@.Analysis.InnerProductSpace.TwoDim._hyg.50'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.opaque'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.instance'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.axiom'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.example'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.inductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.classInductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.structure'-/-- failed to format: format: uncaught backtrack exception
theorem inner_right_angle_rotation_swap ( x y : E ) : ⟪ x , J y ⟫ = - ⟪ J x , y ⟫ := by simp
#align orientation.inner_right_angle_rotation_swap Orientation.inner_right_angle_rotation_swap

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers [] [] [] [] [] [])
     (Command.theorem
      "theorem"
      (Command.declId `inner_right_angle_rotation_swap' [])
      (Command.declSig
       [(Term.explicitBinder "(" [`x `y] [":" `E] [] ")")]
       (Term.typeSpec
        ":"
        («term_=_»
         (RealInnerProductSpace.Analysis.InnerProductSpace.Basic.inner.real
          "⟪"
          (Term.app (Orientation.Analysis.InnerProductSpace.TwoDim.termJ "J") [`x])
          ", "
          `y
          "⟫")
         "="
         («term-_»
          "-"
          (RealInnerProductSpace.Analysis.InnerProductSpace.Basic.inner.real
           "⟪"
           `x
           ", "
           (Term.app (Orientation.Analysis.InnerProductSpace.TwoDim.termJ "J") [`y])
           "⟫")))))
      (Command.declValSimple
       ":="
       (Term.byTactic
        "by"
        (Tactic.tacticSeq
         (Tactic.tacticSeq1Indented
          [(Tactic.simp
            "simp"
            []
            []
            []
            ["["
             [(Tactic.simpLemma [] [] (Term.app `o.inner_right_angle_rotation_swap [`x `y]))]
             "]"]
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
         [(Tactic.simp
           "simp"
           []
           []
           []
           ["["
            [(Tactic.simpLemma [] [] (Term.app `o.inner_right_angle_rotation_swap [`x `y]))]
            "]"]
           [])])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.simp
       "simp"
       []
       []
       []
       ["[" [(Tactic.simpLemma [] [] (Term.app `o.inner_right_angle_rotation_swap [`x `y]))] "]"]
       [])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `o.inner_right_angle_rotation_swap [`x `y])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `y
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `x
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `o.inner_right_angle_rotation_swap
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, tactic) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
      («term_=_»
       (RealInnerProductSpace.Analysis.InnerProductSpace.Basic.inner.real
        "⟪"
        (Term.app (Orientation.Analysis.InnerProductSpace.TwoDim.termJ "J") [`x])
        ", "
        `y
        "⟫")
       "="
       («term-_»
        "-"
        (RealInnerProductSpace.Analysis.InnerProductSpace.Basic.inner.real
         "⟪"
         `x
         ", "
         (Term.app (Orientation.Analysis.InnerProductSpace.TwoDim.termJ "J") [`y])
         "⟫")))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term-_»
       "-"
       (RealInnerProductSpace.Analysis.InnerProductSpace.Basic.inner.real
        "⟪"
        `x
        ", "
        (Term.app (Orientation.Analysis.InnerProductSpace.TwoDim.termJ "J") [`y])
        "⟫"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (RealInnerProductSpace.Analysis.InnerProductSpace.Basic.inner.real
       "⟪"
       `x
       ", "
       (Term.app (Orientation.Analysis.InnerProductSpace.TwoDim.termJ "J") [`y])
       "⟫")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app (Orientation.Analysis.InnerProductSpace.TwoDim.termJ "J") [`y])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `y
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (Orientation.Analysis.InnerProductSpace.TwoDim.termJ "J")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Orientation.Analysis.InnerProductSpace.TwoDim.termJ', expected 'Orientation.Analysis.InnerProductSpace.TwoDim.termJ._@.Analysis.InnerProductSpace.TwoDim._hyg.50'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.opaque'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.instance'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.axiom'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.example'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.inductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.classInductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.structure'-/-- failed to format: format: uncaught backtrack exception
theorem
  inner_right_angle_rotation_swap'
  ( x y : E ) : ⟪ J x , y ⟫ = - ⟪ x , J y ⟫
  := by simp [ o.inner_right_angle_rotation_swap x y ]
#align orientation.inner_right_angle_rotation_swap' Orientation.inner_right_angle_rotation_swap'

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers [] [] [] [] [] [])
     (Command.theorem
      "theorem"
      (Command.declId `inner_comp_right_angle_rotation [])
      (Command.declSig
       [(Term.explicitBinder "(" [`x `y] [":" `E] [] ")")]
       (Term.typeSpec
        ":"
        («term_=_»
         (RealInnerProductSpace.Analysis.InnerProductSpace.Basic.inner.real
          "⟪"
          (Term.app (Orientation.Analysis.InnerProductSpace.TwoDim.termJ "J") [`x])
          ", "
          (Term.app (Orientation.Analysis.InnerProductSpace.TwoDim.termJ "J") [`y])
          "⟫")
         "="
         (RealInnerProductSpace.Analysis.InnerProductSpace.Basic.inner.real "⟪" `x ", " `y "⟫"))))
      (Command.declValSimple
       ":="
       (Term.app
        `LinearIsometryEquiv.inner_map_map
        [(Orientation.Analysis.InnerProductSpace.TwoDim.termJ "J") `x `y])
       [])
      []
      []))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.abbrev'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.def'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       `LinearIsometryEquiv.inner_map_map
       [(Orientation.Analysis.InnerProductSpace.TwoDim.termJ "J") `x `y])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `y
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `x
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Orientation.Analysis.InnerProductSpace.TwoDim.termJ', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Orientation.Analysis.InnerProductSpace.TwoDim.termJ', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Orientation.Analysis.InnerProductSpace.TwoDim.termJ "J")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Orientation.Analysis.InnerProductSpace.TwoDim.termJ', expected 'Orientation.Analysis.InnerProductSpace.TwoDim.termJ._@.Analysis.InnerProductSpace.TwoDim._hyg.50'
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
  inner_comp_right_angle_rotation
  ( x y : E ) : ⟪ J x , J y ⟫ = ⟪ x , y ⟫
  := LinearIsometryEquiv.inner_map_map J x y
#align orientation.inner_comp_right_angle_rotation Orientation.inner_comp_right_angle_rotation

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers
      []
      [(Term.attributes "@[" [(Term.attrInstance (Term.attrKind []) (Attr.simp "simp" [] []))] "]")]
      []
      []
      []
      [])
     (Command.theorem
      "theorem"
      (Command.declId `area_form_right_angle_rotation_left [])
      (Command.declSig
       [(Term.explicitBinder "(" [`x `y] [":" `E] [] ")")]
       (Term.typeSpec
        ":"
        («term_=_»
         (Term.app
          (Orientation.Analysis.InnerProductSpace.TwoDim.termω "ω")
          [(Term.app (Orientation.Analysis.InnerProductSpace.TwoDim.termJ "J") [`x]) `y])
         "="
         («term-_»
          "-"
          (RealInnerProductSpace.Analysis.InnerProductSpace.Basic.inner.real "⟪" `x ", " `y "⟫")))))
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
             [(Tactic.rwRule [(patternIgnore (token.«← » "←"))] `o.inner_comp_right_angle_rotation)
              ","
              (Tactic.rwRule [] `o.inner_right_angle_rotation_right)
              ","
              (Tactic.rwRule [] `neg_neg)]
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
            [(Tactic.rwRule [(patternIgnore (token.«← » "←"))] `o.inner_comp_right_angle_rotation)
             ","
             (Tactic.rwRule [] `o.inner_right_angle_rotation_right)
             ","
             (Tactic.rwRule [] `neg_neg)]
            "]")
           [])])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.rwSeq
       "rw"
       []
       (Tactic.rwRuleSeq
        "["
        [(Tactic.rwRule [(patternIgnore (token.«← » "←"))] `o.inner_comp_right_angle_rotation)
         ","
         (Tactic.rwRule [] `o.inner_right_angle_rotation_right)
         ","
         (Tactic.rwRule [] `neg_neg)]
        "]")
       [])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `neg_neg
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `o.inner_right_angle_rotation_right
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `o.inner_comp_right_angle_rotation
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, tactic) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
      («term_=_»
       (Term.app
        (Orientation.Analysis.InnerProductSpace.TwoDim.termω "ω")
        [(Term.app (Orientation.Analysis.InnerProductSpace.TwoDim.termJ "J") [`x]) `y])
       "="
       («term-_»
        "-"
        (RealInnerProductSpace.Analysis.InnerProductSpace.Basic.inner.real "⟪" `x ", " `y "⟫")))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term-_»
       "-"
       (RealInnerProductSpace.Analysis.InnerProductSpace.Basic.inner.real "⟪" `x ", " `y "⟫"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (RealInnerProductSpace.Analysis.InnerProductSpace.Basic.inner.real "⟪" `x ", " `y "⟫")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `y
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `x
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 75 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 51 >? 75, (some 75, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 50, term))
      (Term.app
       (Orientation.Analysis.InnerProductSpace.TwoDim.termω "ω")
       [(Term.app (Orientation.Analysis.InnerProductSpace.TwoDim.termJ "J") [`x]) `y])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `y
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.app (Orientation.Analysis.InnerProductSpace.TwoDim.termJ "J") [`x])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `x
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (Orientation.Analysis.InnerProductSpace.TwoDim.termJ "J")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Orientation.Analysis.InnerProductSpace.TwoDim.termJ', expected 'Orientation.Analysis.InnerProductSpace.TwoDim.termJ._@.Analysis.InnerProductSpace.TwoDim._hyg.50'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.opaque'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.instance'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.axiom'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.example'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.inductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.classInductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.structure'-/-- failed to format: format: uncaught backtrack exception
@[ simp ]
  theorem
    area_form_right_angle_rotation_left
    ( x y : E ) : ω J x y = - ⟪ x , y ⟫
    := by rw [ ← o.inner_comp_right_angle_rotation , o.inner_right_angle_rotation_right , neg_neg ]
#align
  orientation.area_form_right_angle_rotation_left Orientation.area_form_right_angle_rotation_left

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers
      []
      [(Term.attributes "@[" [(Term.attrInstance (Term.attrKind []) (Attr.simp "simp" [] []))] "]")]
      []
      []
      []
      [])
     (Command.theorem
      "theorem"
      (Command.declId `area_form_right_angle_rotation_right [])
      (Command.declSig
       [(Term.explicitBinder "(" [`x `y] [":" `E] [] ")")]
       (Term.typeSpec
        ":"
        («term_=_»
         (Term.app
          (Orientation.Analysis.InnerProductSpace.TwoDim.termω "ω")
          [`x (Term.app (Orientation.Analysis.InnerProductSpace.TwoDim.termJ "J") [`y])])
         "="
         (RealInnerProductSpace.Analysis.InnerProductSpace.Basic.inner.real "⟪" `x ", " `y "⟫"))))
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
             [(Tactic.rwRule [(patternIgnore (token.«← » "←"))] `o.inner_right_angle_rotation_left)
              ","
              (Tactic.rwRule [] `o.inner_comp_right_angle_rotation)]
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
            [(Tactic.rwRule [(patternIgnore (token.«← » "←"))] `o.inner_right_angle_rotation_left)
             ","
             (Tactic.rwRule [] `o.inner_comp_right_angle_rotation)]
            "]")
           [])])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.rwSeq
       "rw"
       []
       (Tactic.rwRuleSeq
        "["
        [(Tactic.rwRule [(patternIgnore (token.«← » "←"))] `o.inner_right_angle_rotation_left)
         ","
         (Tactic.rwRule [] `o.inner_comp_right_angle_rotation)]
        "]")
       [])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `o.inner_comp_right_angle_rotation
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `o.inner_right_angle_rotation_left
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, tactic) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
      («term_=_»
       (Term.app
        (Orientation.Analysis.InnerProductSpace.TwoDim.termω "ω")
        [`x (Term.app (Orientation.Analysis.InnerProductSpace.TwoDim.termJ "J") [`y])])
       "="
       (RealInnerProductSpace.Analysis.InnerProductSpace.Basic.inner.real "⟪" `x ", " `y "⟫"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (RealInnerProductSpace.Analysis.InnerProductSpace.Basic.inner.real "⟪" `x ", " `y "⟫")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `y
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `x
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 50, term))
      (Term.app
       (Orientation.Analysis.InnerProductSpace.TwoDim.termω "ω")
       [`x (Term.app (Orientation.Analysis.InnerProductSpace.TwoDim.termJ "J") [`y])])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app (Orientation.Analysis.InnerProductSpace.TwoDim.termJ "J") [`y])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `y
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (Orientation.Analysis.InnerProductSpace.TwoDim.termJ "J")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Orientation.Analysis.InnerProductSpace.TwoDim.termJ', expected 'Orientation.Analysis.InnerProductSpace.TwoDim.termJ._@.Analysis.InnerProductSpace.TwoDim._hyg.50'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.opaque'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.instance'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.axiom'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.example'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.inductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.classInductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.structure'-/-- failed to format: format: uncaught backtrack exception
@[ simp ]
  theorem
    area_form_right_angle_rotation_right
    ( x y : E ) : ω x J y = ⟪ x , y ⟫
    := by rw [ ← o.inner_right_angle_rotation_left , o.inner_comp_right_angle_rotation ]
#align
  orientation.area_form_right_angle_rotation_right Orientation.area_form_right_angle_rotation_right

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers
      []
      [(Term.attributes "@[" [(Term.attrInstance (Term.attrKind []) (Attr.simp "simp" [] []))] "]")]
      []
      []
      []
      [])
     (Command.theorem
      "theorem"
      (Command.declId `area_form_comp_right_angle_rotation [])
      (Command.declSig
       [(Term.explicitBinder "(" [`x `y] [":" `E] [] ")")]
       (Term.typeSpec
        ":"
        («term_=_»
         (Term.app
          (Orientation.Analysis.InnerProductSpace.TwoDim.termω "ω")
          [(Term.app (Orientation.Analysis.InnerProductSpace.TwoDim.termJ "J") [`x])
           (Term.app (Orientation.Analysis.InnerProductSpace.TwoDim.termJ "J") [`y])])
         "="
         (Term.app (Orientation.Analysis.InnerProductSpace.TwoDim.termω "ω") [`x `y]))))
      (Command.declValSimple
       ":="
       (Term.byTactic
        "by"
        (Tactic.tacticSeq (Tactic.tacticSeq1Indented [(Tactic.simp "simp" [] [] [] [] [])])))
       [])
      []
      []))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.abbrev'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.def'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.byTactic
       "by"
       (Tactic.tacticSeq (Tactic.tacticSeq1Indented [(Tactic.simp "simp" [] [] [] [] [])])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.simp "simp" [] [] [] [] [])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, tactic) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
      («term_=_»
       (Term.app
        (Orientation.Analysis.InnerProductSpace.TwoDim.termω "ω")
        [(Term.app (Orientation.Analysis.InnerProductSpace.TwoDim.termJ "J") [`x])
         (Term.app (Orientation.Analysis.InnerProductSpace.TwoDim.termJ "J") [`y])])
       "="
       (Term.app (Orientation.Analysis.InnerProductSpace.TwoDim.termω "ω") [`x `y]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app (Orientation.Analysis.InnerProductSpace.TwoDim.termω "ω") [`x `y])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `y
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `x
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (Orientation.Analysis.InnerProductSpace.TwoDim.termω "ω")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Orientation.Analysis.InnerProductSpace.TwoDim.termω', expected 'Orientation.Analysis.InnerProductSpace.TwoDim.termω._@.Analysis.InnerProductSpace.TwoDim._hyg.7'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.opaque'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.instance'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.axiom'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.example'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.inductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.classInductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.structure'-/-- failed to format: format: uncaught backtrack exception
@[ simp ] theorem area_form_comp_right_angle_rotation ( x y : E ) : ω J x J y = ω x y := by simp
#align
  orientation.area_form_comp_right_angle_rotation Orientation.area_form_comp_right_angle_rotation

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers
      []
      [(Term.attributes "@[" [(Term.attrInstance (Term.attrKind []) (Attr.simp "simp" [] []))] "]")]
      []
      []
      []
      [])
     (Command.theorem
      "theorem"
      (Command.declId `right_angle_rotation_trans_right_angle_rotation [])
      (Command.declSig
       []
       (Term.typeSpec
        ":"
        («term_=_»
         (Term.app
          `LinearIsometryEquiv.trans
          [(Orientation.Analysis.InnerProductSpace.TwoDim.termJ "J")
           (Orientation.Analysis.InnerProductSpace.TwoDim.termJ "J")])
         "="
         (Term.app `LinearIsometryEquiv.neg [(Data.Real.Basic.termℝ "ℝ")]))))
      (Command.declValSimple
       ":="
       (Term.byTactic
        "by"
        (Tactic.tacticSeq
         (Tactic.tacticSeq1Indented
          [(Tactic.«tactic_<;>_»
            (Std.Tactic.Ext.«tacticExt___:_» "ext" [] [])
            "<;>"
            (Tactic.simp "simp" [] [] [] [] []))])))
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
         [(Tactic.«tactic_<;>_»
           (Std.Tactic.Ext.«tacticExt___:_» "ext" [] [])
           "<;>"
           (Tactic.simp "simp" [] [] [] [] []))])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.«tactic_<;>_»
       (Std.Tactic.Ext.«tacticExt___:_» "ext" [] [])
       "<;>"
       (Tactic.simp "simp" [] [] [] [] []))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.simp "simp" [] [] [] [] [])
[PrettyPrinter.parenthesize] ...precedences are 2 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1, tactic))
      (Std.Tactic.Ext.«tacticExt___:_» "ext" [] [])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, tactic) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
      («term_=_»
       (Term.app
        `LinearIsometryEquiv.trans
        [(Orientation.Analysis.InnerProductSpace.TwoDim.termJ "J")
         (Orientation.Analysis.InnerProductSpace.TwoDim.termJ "J")])
       "="
       (Term.app `LinearIsometryEquiv.neg [(Data.Real.Basic.termℝ "ℝ")]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `LinearIsometryEquiv.neg [(Data.Real.Basic.termℝ "ℝ")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Data.Real.Basic.termℝ', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Data.Real.Basic.termℝ', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Data.Real.Basic.termℝ "ℝ")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `LinearIsometryEquiv.neg
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 50, term))
      (Term.app
       `LinearIsometryEquiv.trans
       [(Orientation.Analysis.InnerProductSpace.TwoDim.termJ "J")
        (Orientation.Analysis.InnerProductSpace.TwoDim.termJ "J")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Orientation.Analysis.InnerProductSpace.TwoDim.termJ', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Orientation.Analysis.InnerProductSpace.TwoDim.termJ', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Orientation.Analysis.InnerProductSpace.TwoDim.termJ "J")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Orientation.Analysis.InnerProductSpace.TwoDim.termJ', expected 'Orientation.Analysis.InnerProductSpace.TwoDim.termJ._@.Analysis.InnerProductSpace.TwoDim._hyg.50'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.opaque'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.instance'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.axiom'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.example'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.inductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.classInductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.structure'-/-- failed to format: format: uncaught backtrack exception
@[ simp ]
  theorem
    right_angle_rotation_trans_right_angle_rotation
    : LinearIsometryEquiv.trans J J = LinearIsometryEquiv.neg ℝ
    := by ext <;> simp
#align
  orientation.right_angle_rotation_trans_right_angle_rotation Orientation.right_angle_rotation_trans_right_angle_rotation

theorem right_angle_rotation_neg_orientation (x : E) :
    (-o).rightAngleRotation x = -o.rightAngleRotation x :=
  by
  apply ext_inner_right ℝ
  intro y
  rw [inner_right_angle_rotation_left]
  simp
#align
  orientation.right_angle_rotation_neg_orientation Orientation.right_angle_rotation_neg_orientation

@[simp]
theorem right_angle_rotation_trans_neg_orientation :
    (-o).rightAngleRotation = o.rightAngleRotation.trans (LinearIsometryEquiv.neg ℝ) :=
  LinearIsometryEquiv.ext <| o.right_angle_rotation_neg_orientation
#align
  orientation.right_angle_rotation_trans_neg_orientation Orientation.right_angle_rotation_trans_neg_orientation

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers [] [] [] [] [] [])
     (Command.theorem
      "theorem"
      (Command.declId `right_angle_rotation_map [])
      (Command.declSig
       [(Term.implicitBinder "{" [`F] [":" (Term.type "Type" [(Level.hole "_")])] "}")
        (Term.instBinder "[" [] (Term.app `InnerProductSpace [(Data.Real.Basic.termℝ "ℝ") `F]) "]")
        (Term.instBinder
         "["
         []
         (Term.app
          `Fact
          [(«term_=_» (Term.app `finrank [(Data.Real.Basic.termℝ "ℝ") `F]) "=" (num "2"))])
         "]")
        (Term.explicitBinder
         "("
         [`φ]
         [":"
          (Analysis.NormedSpace.LinearIsometry.«term_≃ₗᵢ[_]_»
           `E
           " ≃ₗᵢ["
           (Data.Real.Basic.termℝ "ℝ")
           "] "
           `F)]
         []
         ")")
        (Term.explicitBinder "(" [`x] [":" `F] [] ")")]
       (Term.typeSpec
        ":"
        («term_=_»
         (Term.app
          (Term.proj
           (Term.app
            `Orientation.map
            [(Term.app `Fin [(num "2")]) (Term.proj `φ "." `toLinearEquiv) `o])
           "."
           `rightAngleRotation)
          [`x])
         "="
         (Term.app
          `φ
          [(Term.app
            (Term.proj `o "." `rightAngleRotation)
            [(Term.app (Term.proj `φ "." `symm) [`x])])]))))
      (Command.declValSimple
       ":="
       (Term.byTactic
        "by"
        (Tactic.tacticSeq
         (Tactic.tacticSeq1Indented
          [(Tactic.apply "apply" (Term.app `ext_inner_right [(Data.Real.Basic.termℝ "ℝ")]))
           []
           (Tactic.intro "intro" [`y])
           []
           (Tactic.rwSeq
            "rw"
            []
            (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `inner_right_angle_rotation_left)] "]")
            [])
           []
           (Mathlib.Tactic.tacticTrans___
            "trans"
            [(RealInnerProductSpace.Analysis.InnerProductSpace.Basic.inner.real
              "⟪"
              (Term.app
               (Orientation.Analysis.InnerProductSpace.TwoDim.termJ "J")
               [(Term.app `φ.symm [`x])])
              ", "
              (Term.app `φ.symm [`y])
              "⟫")])
           []
           (tactic__
            (cdotTk (patternIgnore (token.«· » "·")))
            [(Tactic.simp
              "simp"
              []
              []
              []
              ["[" [(Tactic.simpLemma [] [] `o.area_form_map)] "]"]
              [])])
           []
           (Mathlib.Tactic.tacticTrans___
            "trans"
            [(RealInnerProductSpace.Analysis.InnerProductSpace.Basic.inner.real
              "⟪"
              (Term.app
               `φ
               [(Term.app
                 (Orientation.Analysis.InnerProductSpace.TwoDim.termJ "J")
                 [(Term.app `φ.symm [`x])])])
              ", "
              (Term.app `φ [(Term.app `φ.symm [`y])])
              "⟫")])
           []
           (tactic__
            (cdotTk (patternIgnore (token.«· » "·")))
            [(Tactic.rwSeq
              "rw"
              []
              (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `φ.inner_map_map)] "]")
              [])])
           []
           (tactic__
            (cdotTk (patternIgnore (token.«· » "·")))
            [(Tactic.simp "simp" [] [] [] [] [])])])))
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
         [(Tactic.apply "apply" (Term.app `ext_inner_right [(Data.Real.Basic.termℝ "ℝ")]))
          []
          (Tactic.intro "intro" [`y])
          []
          (Tactic.rwSeq
           "rw"
           []
           (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `inner_right_angle_rotation_left)] "]")
           [])
          []
          (Mathlib.Tactic.tacticTrans___
           "trans"
           [(RealInnerProductSpace.Analysis.InnerProductSpace.Basic.inner.real
             "⟪"
             (Term.app
              (Orientation.Analysis.InnerProductSpace.TwoDim.termJ "J")
              [(Term.app `φ.symm [`x])])
             ", "
             (Term.app `φ.symm [`y])
             "⟫")])
          []
          (tactic__
           (cdotTk (patternIgnore (token.«· » "·")))
           [(Tactic.simp "simp" [] [] [] ["[" [(Tactic.simpLemma [] [] `o.area_form_map)] "]"] [])])
          []
          (Mathlib.Tactic.tacticTrans___
           "trans"
           [(RealInnerProductSpace.Analysis.InnerProductSpace.Basic.inner.real
             "⟪"
             (Term.app
              `φ
              [(Term.app
                (Orientation.Analysis.InnerProductSpace.TwoDim.termJ "J")
                [(Term.app `φ.symm [`x])])])
             ", "
             (Term.app `φ [(Term.app `φ.symm [`y])])
             "⟫")])
          []
          (tactic__
           (cdotTk (patternIgnore (token.«· » "·")))
           [(Tactic.rwSeq
             "rw"
             []
             (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `φ.inner_map_map)] "]")
             [])])
          []
          (tactic__
           (cdotTk (patternIgnore (token.«· » "·")))
           [(Tactic.simp "simp" [] [] [] [] [])])])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (tactic__ (cdotTk (patternIgnore (token.«· » "·"))) [(Tactic.simp "simp" [] [] [] [] [])])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.simp "simp" [] [] [] [] [])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (tactic__
       (cdotTk (patternIgnore (token.«· » "·")))
       [(Tactic.rwSeq "rw" [] (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `φ.inner_map_map)] "]") [])])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.rwSeq "rw" [] (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `φ.inner_map_map)] "]") [])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `φ.inner_map_map
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Mathlib.Tactic.tacticTrans___
       "trans"
       [(RealInnerProductSpace.Analysis.InnerProductSpace.Basic.inner.real
         "⟪"
         (Term.app
          `φ
          [(Term.app
            (Orientation.Analysis.InnerProductSpace.TwoDim.termJ "J")
            [(Term.app `φ.symm [`x])])])
         ", "
         (Term.app `φ [(Term.app `φ.symm [`y])])
         "⟫")])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (RealInnerProductSpace.Analysis.InnerProductSpace.Basic.inner.real
       "⟪"
       (Term.app
        `φ
        [(Term.app
          (Orientation.Analysis.InnerProductSpace.TwoDim.termJ "J")
          [(Term.app `φ.symm [`x])])])
       ", "
       (Term.app `φ [(Term.app `φ.symm [`y])])
       "⟫")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `φ [(Term.app `φ.symm [`y])])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `φ.symm [`y])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `y
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `φ.symm
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren "(" (Term.app `φ.symm [`y]) ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `φ
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       `φ
       [(Term.app
         (Orientation.Analysis.InnerProductSpace.TwoDim.termJ "J")
         [(Term.app `φ.symm [`x])])])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app (Orientation.Analysis.InnerProductSpace.TwoDim.termJ "J") [(Term.app `φ.symm [`x])])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `φ.symm [`x])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `x
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `φ.symm
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren "(" (Term.app `φ.symm [`x]) ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (Orientation.Analysis.InnerProductSpace.TwoDim.termJ "J")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Orientation.Analysis.InnerProductSpace.TwoDim.termJ', expected 'Orientation.Analysis.InnerProductSpace.TwoDim.termJ._@.Analysis.InnerProductSpace.TwoDim._hyg.50'
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
  right_angle_rotation_map
  { F : Type _ } [ InnerProductSpace ℝ F ] [ Fact finrank ℝ F = 2 ] ( φ : E ≃ₗᵢ[ ℝ ] F ) ( x : F )
    :
      Orientation.map Fin 2 φ . toLinearEquiv o . rightAngleRotation x
        =
        φ o . rightAngleRotation φ . symm x
  :=
    by
      apply ext_inner_right ℝ
        intro y
        rw [ inner_right_angle_rotation_left ]
        trans ⟪ J φ.symm x , φ.symm y ⟫
        · simp [ o.area_form_map ]
        trans ⟪ φ J φ.symm x , φ φ.symm y ⟫
        · rw [ φ.inner_map_map ]
        · simp
#align orientation.right_angle_rotation_map Orientation.right_angle_rotation_map

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers
      [(Command.docComment
        "/--"
        "`J` commutes with any positively-oriented isometric automorphism. -/")]
      []
      []
      []
      []
      [])
     (Command.theorem
      "theorem"
      (Command.declId `linear_isometry_equiv_comp_right_angle_rotation [])
      (Command.declSig
       [(Term.explicitBinder
         "("
         [`φ]
         [":"
          (Analysis.NormedSpace.LinearIsometry.«term_≃ₗᵢ[_]_»
           `E
           " ≃ₗᵢ["
           (Data.Real.Basic.termℝ "ℝ")
           "] "
           `E)]
         []
         ")")
        (Term.explicitBinder
         "("
         [`hφ]
         [":"
          («term_<_»
           (num "0")
           "<"
           (Term.proj
            (Term.typeAscription
             "("
             (Term.proj `φ "." `toLinearEquiv)
             ":"
             [(Algebra.Module.LinearMap.«term_→ₗ[_]_»
               `E
               " →ₗ["
               (Data.Real.Basic.termℝ "ℝ")
               "] "
               `E)]
             ")")
            "."
            `det))]
         []
         ")")
        (Term.explicitBinder "(" [`x] [":" `E] [] ")")]
       (Term.typeSpec
        ":"
        («term_=_»
         (Term.app `φ [(Term.app (Orientation.Analysis.InnerProductSpace.TwoDim.termJ "J") [`x])])
         "="
         (Term.app
          (Orientation.Analysis.InnerProductSpace.TwoDim.termJ "J")
          [(Term.app `φ [`x])]))))
      (Command.declValSimple
       ":="
       (Term.byTactic
        "by"
        (Tactic.tacticSeq
         (Tactic.tacticSeq1Indented
          [(convert
            "convert"
            []
            (Term.proj (Term.app `o.right_angle_rotation_map [`φ (Term.app `φ [`x])]) "." `symm)
            [])
           []
           (tactic__
            (cdotTk (patternIgnore (token.«· » "·")))
            [(Tactic.simp "simp" [] [] [] [] [])])
           []
           (tactic__
            (cdotTk (patternIgnore (token.«· » "·")))
            [(Mathlib.Tactic.tacticSymm_ "symm" [])
             []
             (Std.Tactic.tacticRwa__
              "rwa"
              (Tactic.rwRuleSeq
               "["
               [(Tactic.rwRule
                 [(patternIgnore (token.«← » "←"))]
                 (Term.app `o.map_eq_iff_det_pos [`φ.to_linear_equiv]))]
               "]")
              [(Tactic.location "at" (Tactic.locationHyp [`hφ] []))])
             []
             (Tactic.rwSeq
              "rw"
              []
              (Tactic.rwRuleSeq
               "["
               [(Tactic.rwRule
                 []
                 (Term.app
                  `Fact.out
                  [(«term_=_» (Term.app `finrank [(Data.Real.Basic.termℝ "ℝ") `E]) "=" (num "2"))]))
                ","
                (Tactic.rwRule [] `Fintype.card_fin)]
               "]")
              [])])])))
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
         [(convert
           "convert"
           []
           (Term.proj (Term.app `o.right_angle_rotation_map [`φ (Term.app `φ [`x])]) "." `symm)
           [])
          []
          (tactic__ (cdotTk (patternIgnore (token.«· » "·"))) [(Tactic.simp "simp" [] [] [] [] [])])
          []
          (tactic__
           (cdotTk (patternIgnore (token.«· » "·")))
           [(Mathlib.Tactic.tacticSymm_ "symm" [])
            []
            (Std.Tactic.tacticRwa__
             "rwa"
             (Tactic.rwRuleSeq
              "["
              [(Tactic.rwRule
                [(patternIgnore (token.«← » "←"))]
                (Term.app `o.map_eq_iff_det_pos [`φ.to_linear_equiv]))]
              "]")
             [(Tactic.location "at" (Tactic.locationHyp [`hφ] []))])
            []
            (Tactic.rwSeq
             "rw"
             []
             (Tactic.rwRuleSeq
              "["
              [(Tactic.rwRule
                []
                (Term.app
                 `Fact.out
                 [(«term_=_» (Term.app `finrank [(Data.Real.Basic.termℝ "ℝ") `E]) "=" (num "2"))]))
               ","
               (Tactic.rwRule [] `Fintype.card_fin)]
              "]")
             [])])])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (tactic__
       (cdotTk (patternIgnore (token.«· » "·")))
       [(Mathlib.Tactic.tacticSymm_ "symm" [])
        []
        (Std.Tactic.tacticRwa__
         "rwa"
         (Tactic.rwRuleSeq
          "["
          [(Tactic.rwRule
            [(patternIgnore (token.«← » "←"))]
            (Term.app `o.map_eq_iff_det_pos [`φ.to_linear_equiv]))]
          "]")
         [(Tactic.location "at" (Tactic.locationHyp [`hφ] []))])
        []
        (Tactic.rwSeq
         "rw"
         []
         (Tactic.rwRuleSeq
          "["
          [(Tactic.rwRule
            []
            (Term.app
             `Fact.out
             [(«term_=_» (Term.app `finrank [(Data.Real.Basic.termℝ "ℝ") `E]) "=" (num "2"))]))
           ","
           (Tactic.rwRule [] `Fintype.card_fin)]
          "]")
         [])])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.rwSeq
       "rw"
       []
       (Tactic.rwRuleSeq
        "["
        [(Tactic.rwRule
          []
          (Term.app
           `Fact.out
           [(«term_=_» (Term.app `finrank [(Data.Real.Basic.termℝ "ℝ") `E]) "=" (num "2"))]))
         ","
         (Tactic.rwRule [] `Fintype.card_fin)]
        "]")
       [])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `Fintype.card_fin
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       `Fact.out
       [(«term_=_» (Term.app `finrank [(Data.Real.Basic.termℝ "ℝ") `E]) "=" (num "2"))])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_=_»', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_=_»', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_=_» (Term.app `finrank [(Data.Real.Basic.termℝ "ℝ") `E]) "=" (num "2"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (num "2")
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 50, term))
      (Term.app `finrank [(Data.Real.Basic.termℝ "ℝ") `E])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `E
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Data.Real.Basic.termℝ', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Data.Real.Basic.termℝ', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Data.Real.Basic.termℝ "ℝ")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `finrank
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1022, (some 1023, term) <=? (some 50, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 50, (some 51, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     («term_=_» (Term.app `finrank [(Data.Real.Basic.termℝ "ℝ") `E]) "=" (num "2"))
     ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `Fact.out
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Std.Tactic.tacticRwa__
       "rwa"
       (Tactic.rwRuleSeq
        "["
        [(Tactic.rwRule
          [(patternIgnore (token.«← » "←"))]
          (Term.app `o.map_eq_iff_det_pos [`φ.to_linear_equiv]))]
        "]")
       [(Tactic.location "at" (Tactic.locationHyp [`hφ] []))])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.locationHyp', expected 'Lean.Parser.Tactic.locationWildcard'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `hφ
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `o.map_eq_iff_det_pos [`φ.to_linear_equiv])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `φ.to_linear_equiv
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `o.map_eq_iff_det_pos
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Mathlib.Tactic.tacticSymm_ "symm" [])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (tactic__ (cdotTk (patternIgnore (token.«· » "·"))) [(Tactic.simp "simp" [] [] [] [] [])])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.simp "simp" [] [] [] [] [])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (convert
       "convert"
       []
       (Term.proj (Term.app `o.right_angle_rotation_map [`φ (Term.app `φ [`x])]) "." `symm)
       [])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.proj (Term.app `o.right_angle_rotation_map [`φ (Term.app `φ [`x])]) "." `symm)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.app `o.right_angle_rotation_map [`φ (Term.app `φ [`x])])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `φ [`x])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `x
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `φ
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren "(" (Term.app `φ [`x]) ")")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `φ
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `o.right_angle_rotation_map
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.app `o.right_angle_rotation_map [`φ (Term.paren "(" (Term.app `φ [`x]) ")")])
     ")")
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, tactic) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
      («term_=_»
       (Term.app `φ [(Term.app (Orientation.Analysis.InnerProductSpace.TwoDim.termJ "J") [`x])])
       "="
       (Term.app (Orientation.Analysis.InnerProductSpace.TwoDim.termJ "J") [(Term.app `φ [`x])]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app (Orientation.Analysis.InnerProductSpace.TwoDim.termJ "J") [(Term.app `φ [`x])])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `φ [`x])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `x
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `φ
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren "(" (Term.app `φ [`x]) ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (Orientation.Analysis.InnerProductSpace.TwoDim.termJ "J")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Orientation.Analysis.InnerProductSpace.TwoDim.termJ', expected 'Orientation.Analysis.InnerProductSpace.TwoDim.termJ._@.Analysis.InnerProductSpace.TwoDim._hyg.50'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.opaque'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.instance'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.axiom'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.example'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.inductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.classInductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.structure'-/-- failed to format: format: uncaught backtrack exception
/-- `J` commutes with any positively-oriented isometric automorphism. -/
  theorem
    linear_isometry_equiv_comp_right_angle_rotation
    ( φ : E ≃ₗᵢ[ ℝ ] E ) ( hφ : 0 < ( φ . toLinearEquiv : E →ₗ[ ℝ ] E ) . det ) ( x : E )
      : φ J x = J φ x
    :=
      by
        convert o.right_angle_rotation_map φ φ x . symm
          · simp
          ·
            symm
              rwa [ ← o.map_eq_iff_det_pos φ.to_linear_equiv ] at hφ
              rw [ Fact.out finrank ℝ E = 2 , Fintype.card_fin ]
#align
  orientation.linear_isometry_equiv_comp_right_angle_rotation Orientation.linear_isometry_equiv_comp_right_angle_rotation

theorem right_angle_rotation_map' {F : Type _} [InnerProductSpace ℝ F] [Fact (finrank ℝ F = 2)]
    (φ : E ≃ₗᵢ[ℝ] F) :
    (Orientation.map (Fin 2) φ.toLinearEquiv o).rightAngleRotation =
      (φ.symm.trans o.rightAngleRotation).trans φ :=
  LinearIsometryEquiv.ext <| o.right_angle_rotation_map φ
#align orientation.right_angle_rotation_map' Orientation.right_angle_rotation_map'

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers
      [(Command.docComment
        "/--"
        "`J` commutes with any positively-oriented isometric automorphism. -/")]
      []
      []
      []
      []
      [])
     (Command.theorem
      "theorem"
      (Command.declId `linear_isometry_equiv_comp_right_angle_rotation' [])
      (Command.declSig
       [(Term.explicitBinder
         "("
         [`φ]
         [":"
          (Analysis.NormedSpace.LinearIsometry.«term_≃ₗᵢ[_]_»
           `E
           " ≃ₗᵢ["
           (Data.Real.Basic.termℝ "ℝ")
           "] "
           `E)]
         []
         ")")
        (Term.explicitBinder
         "("
         [`hφ]
         [":"
          («term_<_»
           (num "0")
           "<"
           (Term.proj
            (Term.typeAscription
             "("
             (Term.proj `φ "." `toLinearEquiv)
             ":"
             [(Algebra.Module.LinearMap.«term_→ₗ[_]_»
               `E
               " →ₗ["
               (Data.Real.Basic.termℝ "ℝ")
               "] "
               `E)]
             ")")
            "."
            `det))]
         []
         ")")]
       (Term.typeSpec
        ":"
        («term_=_»
         (Term.app
          `LinearIsometryEquiv.trans
          [(Orientation.Analysis.InnerProductSpace.TwoDim.termJ "J") `φ])
         "="
         (Term.app
          (Term.proj `φ "." `trans)
          [(Orientation.Analysis.InnerProductSpace.TwoDim.termJ "J")]))))
      (Command.declValSimple
       ":="
       («term_<|_»
        `LinearIsometryEquiv.ext
        "<|"
        (Term.app (Term.proj `o "." `linear_isometry_equiv_comp_right_angle_rotation) [`φ `hφ]))
       [])
      []
      []))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.abbrev'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.def'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_<|_»
       `LinearIsometryEquiv.ext
       "<|"
       (Term.app (Term.proj `o "." `linear_isometry_equiv_comp_right_angle_rotation) [`φ `hφ]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app (Term.proj `o "." `linear_isometry_equiv_comp_right_angle_rotation) [`φ `hφ])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `hφ
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `φ
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (Term.proj `o "." `linear_isometry_equiv_comp_right_angle_rotation)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `o
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 10 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 10, term))
      `LinearIsometryEquiv.ext
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 10, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 10, (some 10, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
      («term_=_»
       (Term.app
        `LinearIsometryEquiv.trans
        [(Orientation.Analysis.InnerProductSpace.TwoDim.termJ "J") `φ])
       "="
       (Term.app
        (Term.proj `φ "." `trans)
        [(Orientation.Analysis.InnerProductSpace.TwoDim.termJ "J")]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       (Term.proj `φ "." `trans)
       [(Orientation.Analysis.InnerProductSpace.TwoDim.termJ "J")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Orientation.Analysis.InnerProductSpace.TwoDim.termJ', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Orientation.Analysis.InnerProductSpace.TwoDim.termJ', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Orientation.Analysis.InnerProductSpace.TwoDim.termJ "J")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Orientation.Analysis.InnerProductSpace.TwoDim.termJ', expected 'Orientation.Analysis.InnerProductSpace.TwoDim.termJ._@.Analysis.InnerProductSpace.TwoDim._hyg.50'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.opaque'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.instance'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.axiom'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.example'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.inductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.classInductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.structure'-/-- failed to format: format: uncaught backtrack exception
/-- `J` commutes with any positively-oriented isometric automorphism. -/
  theorem
    linear_isometry_equiv_comp_right_angle_rotation'
    ( φ : E ≃ₗᵢ[ ℝ ] E ) ( hφ : 0 < ( φ . toLinearEquiv : E →ₗ[ ℝ ] E ) . det )
      : LinearIsometryEquiv.trans J φ = φ . trans J
    := LinearIsometryEquiv.ext <| o . linear_isometry_equiv_comp_right_angle_rotation φ hφ
#align
  orientation.linear_isometry_equiv_comp_right_angle_rotation' Orientation.linear_isometry_equiv_comp_right_angle_rotation'

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers
      [(Command.docComment
        "/--"
        "For a nonzero vector `x` in an oriented two-dimensional real inner product space `E`,\n`![x, J x]` forms an (orthogonal) basis for `E`. -/")]
      []
      []
      []
      []
      [])
     (Command.def
      "def"
      (Command.declId `basisRightAngleRotation [])
      (Command.optDeclSig
       [(Term.explicitBinder "(" [`x] [":" `E] [] ")")
        (Term.explicitBinder "(" [`hx] [":" («term_≠_» `x "≠" (num "0"))] [] ")")]
       [(Term.typeSpec
         ":"
         (Term.app `Basis [(Term.app `Fin [(num "2")]) (Data.Real.Basic.termℝ "ℝ") `E]))])
      (Command.declValSimple
       ":="
       (Term.app
        (Term.explicit "@" `basisOfLinearIndependentOfCardEqFinrank)
        [(Data.Real.Basic.termℝ "ℝ")
         (Term.hole "_")
         (Term.hole "_")
         (Term.hole "_")
         (Term.hole "_")
         (Term.hole "_")
         (Term.hole "_")
         (Term.hole "_")
         (Matrix.Data.Fin.VecNotation.«term![_,»
          "!["
          [`x "," (Term.app (Orientation.Analysis.InnerProductSpace.TwoDim.termJ "J") [`x])]
          "]")
         (Term.app
          `linear_independent_of_ne_zero_of_inner_eq_zero
          [(Term.fun
            "fun"
            (Term.basicFun
             [`i]
             []
             "=>"
             (Term.byTactic
              "by"
              (Tactic.tacticSeq
               (Tactic.tacticSeq1Indented
                [(Tactic.«tactic_<;>_»
                  (Lean.Elab.Tactic.finCases "fin_cases" [`i] [])
                  "<;>"
                  (Tactic.simp "simp" [] [] [] ["[" [(Tactic.simpLemma [] [] `hx)] "]"] []))])))))
           (Term.byTactic
            "by"
            (Tactic.tacticSeq
             (Tactic.tacticSeq1Indented
              [(Tactic.intro "intro" [`i `j `hij])
               []
               (Tactic.«tactic_<;>_»
                (Lean.Elab.Tactic.finCases "fin_cases" [`i] [])
                "<;>"
                (Lean.Elab.Tactic.finCases "fin_cases" [`j] []))
               []
               (tactic__
                (cdotTk (patternIgnore (token.«· » "·")))
                [(Std.Tactic.Simpa.simpa
                  "simpa"
                  []
                  []
                  (Std.Tactic.Simpa.simpaArgsRest [] [] [] [] []))])
               []
               (tactic__
                (cdotTk (patternIgnore (token.«· » "·")))
                [(Tactic.simp "simp" [] [] [] [] [])])
               []
               (tactic__
                (cdotTk (patternIgnore (token.«· » "·")))
                [(Tactic.simp "simp" [] [] [] [] [])])
               []
               (tactic__
                (cdotTk (patternIgnore (token.«· » "·")))
                [(Std.Tactic.Simpa.simpa
                  "simpa"
                  []
                  []
                  (Std.Tactic.Simpa.simpaArgsRest [] [] [] [] []))])])))])
         (Term.proj
          (Term.app
           `Fact.out
           [(«term_=_» (Term.app `finrank [(Data.Real.Basic.termℝ "ℝ") `E]) "=" (num "2"))])
          "."
          `symm)])
       [])
      []
      []
      []))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.abbrev'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       (Term.explicit "@" `basisOfLinearIndependentOfCardEqFinrank)
       [(Data.Real.Basic.termℝ "ℝ")
        (Term.hole "_")
        (Term.hole "_")
        (Term.hole "_")
        (Term.hole "_")
        (Term.hole "_")
        (Term.hole "_")
        (Term.hole "_")
        (Matrix.Data.Fin.VecNotation.«term![_,»
         "!["
         [`x "," (Term.app (Orientation.Analysis.InnerProductSpace.TwoDim.termJ "J") [`x])]
         "]")
        (Term.app
         `linear_independent_of_ne_zero_of_inner_eq_zero
         [(Term.fun
           "fun"
           (Term.basicFun
            [`i]
            []
            "=>"
            (Term.byTactic
             "by"
             (Tactic.tacticSeq
              (Tactic.tacticSeq1Indented
               [(Tactic.«tactic_<;>_»
                 (Lean.Elab.Tactic.finCases "fin_cases" [`i] [])
                 "<;>"
                 (Tactic.simp "simp" [] [] [] ["[" [(Tactic.simpLemma [] [] `hx)] "]"] []))])))))
          (Term.byTactic
           "by"
           (Tactic.tacticSeq
            (Tactic.tacticSeq1Indented
             [(Tactic.intro "intro" [`i `j `hij])
              []
              (Tactic.«tactic_<;>_»
               (Lean.Elab.Tactic.finCases "fin_cases" [`i] [])
               "<;>"
               (Lean.Elab.Tactic.finCases "fin_cases" [`j] []))
              []
              (tactic__
               (cdotTk (patternIgnore (token.«· » "·")))
               [(Std.Tactic.Simpa.simpa
                 "simpa"
                 []
                 []
                 (Std.Tactic.Simpa.simpaArgsRest [] [] [] [] []))])
              []
              (tactic__
               (cdotTk (patternIgnore (token.«· » "·")))
               [(Tactic.simp "simp" [] [] [] [] [])])
              []
              (tactic__
               (cdotTk (patternIgnore (token.«· » "·")))
               [(Tactic.simp "simp" [] [] [] [] [])])
              []
              (tactic__
               (cdotTk (patternIgnore (token.«· » "·")))
               [(Std.Tactic.Simpa.simpa
                 "simpa"
                 []
                 []
                 (Std.Tactic.Simpa.simpaArgsRest [] [] [] [] []))])])))])
        (Term.proj
         (Term.app
          `Fact.out
          [(«term_=_» (Term.app `finrank [(Data.Real.Basic.termℝ "ℝ") `E]) "=" (num "2"))])
         "."
         `symm)])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.proj', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.proj', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.proj
       (Term.app
        `Fact.out
        [(«term_=_» (Term.app `finrank [(Data.Real.Basic.termℝ "ℝ") `E]) "=" (num "2"))])
       "."
       `symm)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.app
       `Fact.out
       [(«term_=_» (Term.app `finrank [(Data.Real.Basic.termℝ "ℝ") `E]) "=" (num "2"))])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_=_»', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_=_»', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_=_» (Term.app `finrank [(Data.Real.Basic.termℝ "ℝ") `E]) "=" (num "2"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (num "2")
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 50, term))
      (Term.app `finrank [(Data.Real.Basic.termℝ "ℝ") `E])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `E
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Data.Real.Basic.termℝ', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Data.Real.Basic.termℝ', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Data.Real.Basic.termℝ "ℝ")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `finrank
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1022, (some 1023, term) <=? (some 50, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 50, (some 51, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     («term_=_» (Term.app `finrank [(Data.Real.Basic.termℝ "ℝ") `E]) "=" (num "2"))
     ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `Fact.out
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.app
      `Fact.out
      [(Term.paren
        "("
        («term_=_» (Term.app `finrank [(Data.Real.Basic.termℝ "ℝ") `E]) "=" (num "2"))
        ")")])
     ")")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.app
       `linear_independent_of_ne_zero_of_inner_eq_zero
       [(Term.fun
         "fun"
         (Term.basicFun
          [`i]
          []
          "=>"
          (Term.byTactic
           "by"
           (Tactic.tacticSeq
            (Tactic.tacticSeq1Indented
             [(Tactic.«tactic_<;>_»
               (Lean.Elab.Tactic.finCases "fin_cases" [`i] [])
               "<;>"
               (Tactic.simp "simp" [] [] [] ["[" [(Tactic.simpLemma [] [] `hx)] "]"] []))])))))
        (Term.byTactic
         "by"
         (Tactic.tacticSeq
          (Tactic.tacticSeq1Indented
           [(Tactic.intro "intro" [`i `j `hij])
            []
            (Tactic.«tactic_<;>_»
             (Lean.Elab.Tactic.finCases "fin_cases" [`i] [])
             "<;>"
             (Lean.Elab.Tactic.finCases "fin_cases" [`j] []))
            []
            (tactic__
             (cdotTk (patternIgnore (token.«· » "·")))
             [(Std.Tactic.Simpa.simpa
               "simpa"
               []
               []
               (Std.Tactic.Simpa.simpaArgsRest [] [] [] [] []))])
            []
            (tactic__
             (cdotTk (patternIgnore (token.«· » "·")))
             [(Tactic.simp "simp" [] [] [] [] [])])
            []
            (tactic__
             (cdotTk (patternIgnore (token.«· » "·")))
             [(Tactic.simp "simp" [] [] [] [] [])])
            []
            (tactic__
             (cdotTk (patternIgnore (token.«· » "·")))
             [(Std.Tactic.Simpa.simpa
               "simpa"
               []
               []
               (Std.Tactic.Simpa.simpaArgsRest [] [] [] [] []))])])))])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.byTactic', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.byTactic', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.byTactic
       "by"
       (Tactic.tacticSeq
        (Tactic.tacticSeq1Indented
         [(Tactic.intro "intro" [`i `j `hij])
          []
          (Tactic.«tactic_<;>_»
           (Lean.Elab.Tactic.finCases "fin_cases" [`i] [])
           "<;>"
           (Lean.Elab.Tactic.finCases "fin_cases" [`j] []))
          []
          (tactic__
           (cdotTk (patternIgnore (token.«· » "·")))
           [(Std.Tactic.Simpa.simpa "simpa" [] [] (Std.Tactic.Simpa.simpaArgsRest [] [] [] [] []))])
          []
          (tactic__ (cdotTk (patternIgnore (token.«· » "·"))) [(Tactic.simp "simp" [] [] [] [] [])])
          []
          (tactic__ (cdotTk (patternIgnore (token.«· » "·"))) [(Tactic.simp "simp" [] [] [] [] [])])
          []
          (tactic__
           (cdotTk (patternIgnore (token.«· » "·")))
           [(Std.Tactic.Simpa.simpa
             "simpa"
             []
             []
             (Std.Tactic.Simpa.simpaArgsRest [] [] [] [] []))])])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (tactic__
       (cdotTk (patternIgnore (token.«· » "·")))
       [(Std.Tactic.Simpa.simpa "simpa" [] [] (Std.Tactic.Simpa.simpaArgsRest [] [] [] [] []))])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Std.Tactic.Simpa.simpa "simpa" [] [] (Std.Tactic.Simpa.simpaArgsRest [] [] [] [] []))
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (tactic__ (cdotTk (patternIgnore (token.«· » "·"))) [(Tactic.simp "simp" [] [] [] [] [])])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.simp "simp" [] [] [] [] [])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (tactic__ (cdotTk (patternIgnore (token.«· » "·"))) [(Tactic.simp "simp" [] [] [] [] [])])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.simp "simp" [] [] [] [] [])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (tactic__
       (cdotTk (patternIgnore (token.«· » "·")))
       [(Std.Tactic.Simpa.simpa "simpa" [] [] (Std.Tactic.Simpa.simpaArgsRest [] [] [] [] []))])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Std.Tactic.Simpa.simpa "simpa" [] [] (Std.Tactic.Simpa.simpaArgsRest [] [] [] [] []))
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.«tactic_<;>_»
       (Lean.Elab.Tactic.finCases "fin_cases" [`i] [])
       "<;>"
       (Lean.Elab.Tactic.finCases "fin_cases" [`j] []))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Lean.Elab.Tactic.finCases "fin_cases" [`j] [])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'null', expected 'token.«*»'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `j
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 2 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1, tactic))
      (Lean.Elab.Tactic.finCases "fin_cases" [`i] [])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'null', expected 'token.«*»'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `i
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.intro "intro" [`i `j `hij])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `hij
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `j
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `i
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 0,
     tactic) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.byTactic
      "by"
      (Tactic.tacticSeq
       (Tactic.tacticSeq1Indented
        [(Tactic.intro "intro" [`i `j `hij])
         []
         (Tactic.«tactic_<;>_»
          (Lean.Elab.Tactic.finCases "fin_cases" [`i] [])
          "<;>"
          (Lean.Elab.Tactic.finCases "fin_cases" [`j] []))
         []
         (tactic__
          (cdotTk (patternIgnore (token.«· » "·")))
          [(Std.Tactic.Simpa.simpa "simpa" [] [] (Std.Tactic.Simpa.simpaArgsRest [] [] [] [] []))])
         []
         (tactic__ (cdotTk (patternIgnore (token.«· » "·"))) [(Tactic.simp "simp" [] [] [] [] [])])
         []
         (tactic__ (cdotTk (patternIgnore (token.«· » "·"))) [(Tactic.simp "simp" [] [] [] [] [])])
         []
         (tactic__
          (cdotTk (patternIgnore (token.«· » "·")))
          [(Std.Tactic.Simpa.simpa
            "simpa"
            []
            []
            (Std.Tactic.Simpa.simpaArgsRest [] [] [] [] []))])])))
     ")")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.fun
       "fun"
       (Term.basicFun
        [`i]
        []
        "=>"
        (Term.byTactic
         "by"
         (Tactic.tacticSeq
          (Tactic.tacticSeq1Indented
           [(Tactic.«tactic_<;>_»
             (Lean.Elab.Tactic.finCases "fin_cases" [`i] [])
             "<;>"
             (Tactic.simp "simp" [] [] [] ["[" [(Tactic.simpLemma [] [] `hx)] "]"] []))])))))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.byTactic
       "by"
       (Tactic.tacticSeq
        (Tactic.tacticSeq1Indented
         [(Tactic.«tactic_<;>_»
           (Lean.Elab.Tactic.finCases "fin_cases" [`i] [])
           "<;>"
           (Tactic.simp "simp" [] [] [] ["[" [(Tactic.simpLemma [] [] `hx)] "]"] []))])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.«tactic_<;>_»
       (Lean.Elab.Tactic.finCases "fin_cases" [`i] [])
       "<;>"
       (Tactic.simp "simp" [] [] [] ["[" [(Tactic.simpLemma [] [] `hx)] "]"] []))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.simp "simp" [] [] [] ["[" [(Tactic.simpLemma [] [] `hx)] "]"] [])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `hx
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 2 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1, tactic))
      (Lean.Elab.Tactic.finCases "fin_cases" [`i] [])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'null', expected 'token.«*»'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `i
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, tactic) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.strictImplicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.implicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.instBinder'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `i
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (some 0, term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.fun
      "fun"
      (Term.basicFun
       [`i]
       []
       "=>"
       (Term.byTactic
        "by"
        (Tactic.tacticSeq
         (Tactic.tacticSeq1Indented
          [(Tactic.«tactic_<;>_»
            (Lean.Elab.Tactic.finCases "fin_cases" [`i] [])
            "<;>"
            (Tactic.simp "simp" [] [] [] ["[" [(Tactic.simpLemma [] [] `hx)] "]"] []))])))))
     ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `linear_independent_of_ne_zero_of_inner_eq_zero
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023,
     term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.app
      `linear_independent_of_ne_zero_of_inner_eq_zero
      [(Term.paren
        "("
        (Term.fun
         "fun"
         (Term.basicFun
          [`i]
          []
          "=>"
          (Term.byTactic
           "by"
           (Tactic.tacticSeq
            (Tactic.tacticSeq1Indented
             [(Tactic.«tactic_<;>_»
               (Lean.Elab.Tactic.finCases "fin_cases" [`i] [])
               "<;>"
               (Tactic.simp "simp" [] [] [] ["[" [(Tactic.simpLemma [] [] `hx)] "]"] []))])))))
        ")")
       (Term.paren
        "("
        (Term.byTactic
         "by"
         (Tactic.tacticSeq
          (Tactic.tacticSeq1Indented
           [(Tactic.intro "intro" [`i `j `hij])
            []
            (Tactic.«tactic_<;>_»
             (Lean.Elab.Tactic.finCases "fin_cases" [`i] [])
             "<;>"
             (Lean.Elab.Tactic.finCases "fin_cases" [`j] []))
            []
            (tactic__
             (cdotTk (patternIgnore (token.«· » "·")))
             [(Std.Tactic.Simpa.simpa
               "simpa"
               []
               []
               (Std.Tactic.Simpa.simpaArgsRest [] [] [] [] []))])
            []
            (tactic__
             (cdotTk (patternIgnore (token.«· » "·")))
             [(Tactic.simp "simp" [] [] [] [] [])])
            []
            (tactic__
             (cdotTk (patternIgnore (token.«· » "·")))
             [(Tactic.simp "simp" [] [] [] [] [])])
            []
            (tactic__
             (cdotTk (patternIgnore (token.«· » "·")))
             [(Std.Tactic.Simpa.simpa
               "simpa"
               []
               []
               (Std.Tactic.Simpa.simpaArgsRest [] [] [] [] []))])])))
        ")")])
     ")")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Matrix.Data.Fin.VecNotation.«term![_,»', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Matrix.Data.Fin.VecNotation.«term![_,»', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Matrix.Data.Fin.VecNotation.«term![_,»
       "!["
       [`x "," (Term.app (Orientation.Analysis.InnerProductSpace.TwoDim.termJ "J") [`x])]
       "]")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app (Orientation.Analysis.InnerProductSpace.TwoDim.termJ "J") [`x])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `x
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (Orientation.Analysis.InnerProductSpace.TwoDim.termJ "J")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Orientation.Analysis.InnerProductSpace.TwoDim.termJ', expected 'Orientation.Analysis.InnerProductSpace.TwoDim.termJ._@.Analysis.InnerProductSpace.TwoDim._hyg.50'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.declValSimple', expected 'Lean.Parser.Command.declValEqns'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.declValSimple', expected 'Lean.Parser.Command.whereStructInst'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.theorem'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.opaque'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.instance'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.axiom'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.example'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.inductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.classInductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.structure'-/-- failed to format: format: uncaught backtrack exception
/--
    For a nonzero vector `x` in an oriented two-dimensional real inner product space `E`,
    `![x, J x]` forms an (orthogonal) basis for `E`. -/
  def
    basisRightAngleRotation
    ( x : E ) ( hx : x ≠ 0 ) : Basis Fin 2 ℝ E
    :=
      @ basisOfLinearIndependentOfCardEqFinrank
        ℝ
          _
          _
          _
          _
          _
          _
          _
          ![ x , J x ]
          linear_independent_of_ne_zero_of_inner_eq_zero
            fun i => by fin_cases i <;> simp [ hx ]
              by intro i j hij fin_cases i <;> fin_cases j · simpa · simp · simp · simpa
          Fact.out finrank ℝ E = 2 . symm
#align orientation.basis_right_angle_rotation Orientation.basisRightAngleRotation

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers
      []
      [(Term.attributes "@[" [(Term.attrInstance (Term.attrKind []) (Attr.simp "simp" [] []))] "]")]
      []
      []
      []
      [])
     (Command.theorem
      "theorem"
      (Command.declId `coe_basis_right_angle_rotation [])
      (Command.declSig
       [(Term.explicitBinder "(" [`x] [":" `E] [] ")")
        (Term.explicitBinder "(" [`hx] [":" («term_≠_» `x "≠" (num "0"))] [] ")")]
       (Term.typeSpec
        ":"
        («term_=_»
         (Init.Coe.«term⇑_» "⇑" (Term.app (Term.proj `o "." `basisRightAngleRotation) [`x `hx]))
         "="
         (Matrix.Data.Fin.VecNotation.«term![_,»
          "!["
          [`x "," (Term.app (Orientation.Analysis.InnerProductSpace.TwoDim.termJ "J") [`x])]
          "]"))))
      (Command.declValSimple
       ":="
       (Term.app
        `coe_basis_of_linear_independent_of_card_eq_finrank
        [(Term.hole "_") (Term.hole "_")])
       [])
      []
      []))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.abbrev'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.def'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       `coe_basis_of_linear_independent_of_card_eq_finrank
       [(Term.hole "_") (Term.hole "_")])
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
      `coe_basis_of_linear_independent_of_card_eq_finrank
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
      («term_=_»
       (Init.Coe.«term⇑_» "⇑" (Term.app (Term.proj `o "." `basisRightAngleRotation) [`x `hx]))
       "="
       (Matrix.Data.Fin.VecNotation.«term![_,»
        "!["
        [`x "," (Term.app (Orientation.Analysis.InnerProductSpace.TwoDim.termJ "J") [`x])]
        "]"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Matrix.Data.Fin.VecNotation.«term![_,»
       "!["
       [`x "," (Term.app (Orientation.Analysis.InnerProductSpace.TwoDim.termJ "J") [`x])]
       "]")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app (Orientation.Analysis.InnerProductSpace.TwoDim.termJ "J") [`x])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `x
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (Orientation.Analysis.InnerProductSpace.TwoDim.termJ "J")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Orientation.Analysis.InnerProductSpace.TwoDim.termJ', expected 'Orientation.Analysis.InnerProductSpace.TwoDim.termJ._@.Analysis.InnerProductSpace.TwoDim._hyg.50'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.opaque'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.instance'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.axiom'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.example'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.inductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.classInductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.structure'-/-- failed to format: format: uncaught backtrack exception
@[ simp ]
  theorem
    coe_basis_right_angle_rotation
    ( x : E ) ( hx : x ≠ 0 ) : ⇑ o . basisRightAngleRotation x hx = ![ x , J x ]
    := coe_basis_of_linear_independent_of_card_eq_finrank _ _
#align orientation.coe_basis_right_angle_rotation Orientation.coe_basis_right_angle_rotation

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers
      [(Command.docComment
        "/--"
        "For vectors `a x y : E`, the identity `⟪a, x⟫ * ⟪a, y⟫ + ω a x * ω a y = ‖a‖ ^ 2 * ⟪x, y⟫`. (See\n`orientation.inner_mul_inner_add_area_form_mul_area_form` for the \"applied\" form.)-/")]
      []
      []
      []
      []
      [])
     (Command.theorem
      "theorem"
      (Command.declId `inner_mul_inner_add_area_form_mul_area_form' [])
      (Command.declSig
       [(Term.explicitBinder "(" [`a `x] [":" `E] [] ")")]
       (Term.typeSpec
        ":"
        («term_=_»
         («term_+_»
          (Algebra.Group.Defs.«term_•_»
           (RealInnerProductSpace.Analysis.InnerProductSpace.Basic.inner.real "⟪" `a ", " `x "⟫")
           " • "
           (Term.app
            (Term.explicit "@" `innerₛₗ)
            [(Data.Real.Basic.termℝ "ℝ") (Term.hole "_") (Term.hole "_") (Term.hole "_") `a]))
          "+"
          (Algebra.Group.Defs.«term_•_»
           (Term.app (Orientation.Analysis.InnerProductSpace.TwoDim.termω "ω") [`a `x])
           " • "
           (Term.app (Orientation.Analysis.InnerProductSpace.TwoDim.termω "ω") [`a])))
         "="
         (Algebra.Group.Defs.«term_•_»
          («term_^_» (Analysis.Normed.Group.Basic.«term‖_‖» "‖" `a "‖") "^" (num "2"))
          " • "
          (Term.app
           (Term.explicit "@" `innerₛₗ)
           [(Data.Real.Basic.termℝ "ℝ") (Term.hole "_") (Term.hole "_") (Term.hole "_") `x])))))
      (Command.declValSimple
       ":="
       (Term.byTactic
        "by"
        (Tactic.tacticSeq
         (Tactic.tacticSeq1Indented
          [(Classical.«tacticBy_cases_:_» "by_cases" [`ha ":"] («term_=_» `a "=" (num "0")))
           []
           (tactic__
            (cdotTk (patternIgnore (token.«· » "·")))
            [(Tactic.simp "simp" [] [] [] ["[" [(Tactic.simpLemma [] [] `ha)] "]"] [])])
           []
           (Tactic.apply
            "apply"
            (Term.proj (Term.app `o.basis_right_angle_rotation [`a `ha]) "." `ext))
           []
           (Tactic.intro "intro" [`i])
           []
           (Lean.Elab.Tactic.finCases "fin_cases" [`i] [])
           []
           (tactic__
            (cdotTk (patternIgnore (token.«· » "·")))
            [(Tactic.simp
              "simp"
              []
              []
              ["only"]
              ["["
               [(Tactic.simpLemma [] [] `real_inner_self_eq_norm_sq)
                ","
                (Tactic.simpLemma [] [] `Algebra.id.smul_eq_mul)
                ","
                (Tactic.simpLemma [] [] `innerₛₗ_apply)
                ","
                (Tactic.simpLemma [] [] `LinearMap.smul_apply)
                ","
                (Tactic.simpLemma [] [] `LinearMap.add_apply)
                ","
                (Tactic.simpLemma [] [] `Matrix.cons_val_zero)
                ","
                (Tactic.simpLemma [] [] `o.coe_basis_right_angle_rotation)
                ","
                (Tactic.simpLemma [] [] `o.area_form_apply_self)
                ","
                (Tactic.simpLemma [] [] `real_inner_comm)]
               "]"]
              [])
             []
             (Mathlib.Tactic.RingNF.ring "ring")])
           []
           (tactic__
            (cdotTk (patternIgnore (token.«· » "·")))
            [(Tactic.simp
              "simp"
              []
              []
              ["only"]
              ["["
               [(Tactic.simpLemma [] [] `real_inner_self_eq_norm_sq)
                ","
                (Tactic.simpLemma [] [] `Algebra.id.smul_eq_mul)
                ","
                (Tactic.simpLemma [] [] `innerₛₗ_apply)
                ","
                (Tactic.simpLemma [] [] `LinearMap.smul_apply)
                ","
                (Tactic.simpLemma [] [] `neg_inj)
                ","
                (Tactic.simpLemma [] [] `LinearMap.add_apply)
                ","
                (Tactic.simpLemma [] [] `Matrix.cons_val_one)
                ","
                (Tactic.simpLemma [] [] `Matrix.head_cons)
                ","
                (Tactic.simpLemma [] [] `o.coe_basis_right_angle_rotation)
                ","
                (Tactic.simpLemma [] [] `o.area_form_right_angle_rotation_right)
                ","
                (Tactic.simpLemma [] [] `o.area_form_apply_self)
                ","
                (Tactic.simpLemma [] [] `o.inner_right_angle_rotation_right)]
               "]"]
              [])
             []
             (Tactic.rwSeq
              "rw"
              []
              (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `o.area_form_swap)] "]")
              [])
             []
             (Mathlib.Tactic.RingNF.ring "ring")])])))
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
         [(Classical.«tacticBy_cases_:_» "by_cases" [`ha ":"] («term_=_» `a "=" (num "0")))
          []
          (tactic__
           (cdotTk (patternIgnore (token.«· » "·")))
           [(Tactic.simp "simp" [] [] [] ["[" [(Tactic.simpLemma [] [] `ha)] "]"] [])])
          []
          (Tactic.apply
           "apply"
           (Term.proj (Term.app `o.basis_right_angle_rotation [`a `ha]) "." `ext))
          []
          (Tactic.intro "intro" [`i])
          []
          (Lean.Elab.Tactic.finCases "fin_cases" [`i] [])
          []
          (tactic__
           (cdotTk (patternIgnore (token.«· » "·")))
           [(Tactic.simp
             "simp"
             []
             []
             ["only"]
             ["["
              [(Tactic.simpLemma [] [] `real_inner_self_eq_norm_sq)
               ","
               (Tactic.simpLemma [] [] `Algebra.id.smul_eq_mul)
               ","
               (Tactic.simpLemma [] [] `innerₛₗ_apply)
               ","
               (Tactic.simpLemma [] [] `LinearMap.smul_apply)
               ","
               (Tactic.simpLemma [] [] `LinearMap.add_apply)
               ","
               (Tactic.simpLemma [] [] `Matrix.cons_val_zero)
               ","
               (Tactic.simpLemma [] [] `o.coe_basis_right_angle_rotation)
               ","
               (Tactic.simpLemma [] [] `o.area_form_apply_self)
               ","
               (Tactic.simpLemma [] [] `real_inner_comm)]
              "]"]
             [])
            []
            (Mathlib.Tactic.RingNF.ring "ring")])
          []
          (tactic__
           (cdotTk (patternIgnore (token.«· » "·")))
           [(Tactic.simp
             "simp"
             []
             []
             ["only"]
             ["["
              [(Tactic.simpLemma [] [] `real_inner_self_eq_norm_sq)
               ","
               (Tactic.simpLemma [] [] `Algebra.id.smul_eq_mul)
               ","
               (Tactic.simpLemma [] [] `innerₛₗ_apply)
               ","
               (Tactic.simpLemma [] [] `LinearMap.smul_apply)
               ","
               (Tactic.simpLemma [] [] `neg_inj)
               ","
               (Tactic.simpLemma [] [] `LinearMap.add_apply)
               ","
               (Tactic.simpLemma [] [] `Matrix.cons_val_one)
               ","
               (Tactic.simpLemma [] [] `Matrix.head_cons)
               ","
               (Tactic.simpLemma [] [] `o.coe_basis_right_angle_rotation)
               ","
               (Tactic.simpLemma [] [] `o.area_form_right_angle_rotation_right)
               ","
               (Tactic.simpLemma [] [] `o.area_form_apply_self)
               ","
               (Tactic.simpLemma [] [] `o.inner_right_angle_rotation_right)]
              "]"]
             [])
            []
            (Tactic.rwSeq
             "rw"
             []
             (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `o.area_form_swap)] "]")
             [])
            []
            (Mathlib.Tactic.RingNF.ring "ring")])])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (tactic__
       (cdotTk (patternIgnore (token.«· » "·")))
       [(Tactic.simp
         "simp"
         []
         []
         ["only"]
         ["["
          [(Tactic.simpLemma [] [] `real_inner_self_eq_norm_sq)
           ","
           (Tactic.simpLemma [] [] `Algebra.id.smul_eq_mul)
           ","
           (Tactic.simpLemma [] [] `innerₛₗ_apply)
           ","
           (Tactic.simpLemma [] [] `LinearMap.smul_apply)
           ","
           (Tactic.simpLemma [] [] `neg_inj)
           ","
           (Tactic.simpLemma [] [] `LinearMap.add_apply)
           ","
           (Tactic.simpLemma [] [] `Matrix.cons_val_one)
           ","
           (Tactic.simpLemma [] [] `Matrix.head_cons)
           ","
           (Tactic.simpLemma [] [] `o.coe_basis_right_angle_rotation)
           ","
           (Tactic.simpLemma [] [] `o.area_form_right_angle_rotation_right)
           ","
           (Tactic.simpLemma [] [] `o.area_form_apply_self)
           ","
           (Tactic.simpLemma [] [] `o.inner_right_angle_rotation_right)]
          "]"]
         [])
        []
        (Tactic.rwSeq "rw" [] (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `o.area_form_swap)] "]") [])
        []
        (Mathlib.Tactic.RingNF.ring "ring")])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Mathlib.Tactic.RingNF.ring "ring")
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.rwSeq "rw" [] (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `o.area_form_swap)] "]") [])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `o.area_form_swap
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
        [(Tactic.simpLemma [] [] `real_inner_self_eq_norm_sq)
         ","
         (Tactic.simpLemma [] [] `Algebra.id.smul_eq_mul)
         ","
         (Tactic.simpLemma [] [] `innerₛₗ_apply)
         ","
         (Tactic.simpLemma [] [] `LinearMap.smul_apply)
         ","
         (Tactic.simpLemma [] [] `neg_inj)
         ","
         (Tactic.simpLemma [] [] `LinearMap.add_apply)
         ","
         (Tactic.simpLemma [] [] `Matrix.cons_val_one)
         ","
         (Tactic.simpLemma [] [] `Matrix.head_cons)
         ","
         (Tactic.simpLemma [] [] `o.coe_basis_right_angle_rotation)
         ","
         (Tactic.simpLemma [] [] `o.area_form_right_angle_rotation_right)
         ","
         (Tactic.simpLemma [] [] `o.area_form_apply_self)
         ","
         (Tactic.simpLemma [] [] `o.inner_right_angle_rotation_right)]
        "]"]
       [])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `o.inner_right_angle_rotation_right
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `o.area_form_apply_self
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `o.area_form_right_angle_rotation_right
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `o.coe_basis_right_angle_rotation
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `Matrix.head_cons
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `Matrix.cons_val_one
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `LinearMap.add_apply
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `neg_inj
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `LinearMap.smul_apply
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `innerₛₗ_apply
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `Algebra.id.smul_eq_mul
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `real_inner_self_eq_norm_sq
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (tactic__
       (cdotTk (patternIgnore (token.«· » "·")))
       [(Tactic.simp
         "simp"
         []
         []
         ["only"]
         ["["
          [(Tactic.simpLemma [] [] `real_inner_self_eq_norm_sq)
           ","
           (Tactic.simpLemma [] [] `Algebra.id.smul_eq_mul)
           ","
           (Tactic.simpLemma [] [] `innerₛₗ_apply)
           ","
           (Tactic.simpLemma [] [] `LinearMap.smul_apply)
           ","
           (Tactic.simpLemma [] [] `LinearMap.add_apply)
           ","
           (Tactic.simpLemma [] [] `Matrix.cons_val_zero)
           ","
           (Tactic.simpLemma [] [] `o.coe_basis_right_angle_rotation)
           ","
           (Tactic.simpLemma [] [] `o.area_form_apply_self)
           ","
           (Tactic.simpLemma [] [] `real_inner_comm)]
          "]"]
         [])
        []
        (Mathlib.Tactic.RingNF.ring "ring")])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Mathlib.Tactic.RingNF.ring "ring")
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.simp
       "simp"
       []
       []
       ["only"]
       ["["
        [(Tactic.simpLemma [] [] `real_inner_self_eq_norm_sq)
         ","
         (Tactic.simpLemma [] [] `Algebra.id.smul_eq_mul)
         ","
         (Tactic.simpLemma [] [] `innerₛₗ_apply)
         ","
         (Tactic.simpLemma [] [] `LinearMap.smul_apply)
         ","
         (Tactic.simpLemma [] [] `LinearMap.add_apply)
         ","
         (Tactic.simpLemma [] [] `Matrix.cons_val_zero)
         ","
         (Tactic.simpLemma [] [] `o.coe_basis_right_angle_rotation)
         ","
         (Tactic.simpLemma [] [] `o.area_form_apply_self)
         ","
         (Tactic.simpLemma [] [] `real_inner_comm)]
        "]"]
       [])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `real_inner_comm
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `o.area_form_apply_self
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `o.coe_basis_right_angle_rotation
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `Matrix.cons_val_zero
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `LinearMap.add_apply
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `LinearMap.smul_apply
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `innerₛₗ_apply
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `Algebra.id.smul_eq_mul
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `real_inner_self_eq_norm_sq
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Lean.Elab.Tactic.finCases "fin_cases" [`i] [])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'null', expected 'token.«*»'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `i
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.intro "intro" [`i])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `i
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.apply "apply" (Term.proj (Term.app `o.basis_right_angle_rotation [`a `ha]) "." `ext))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.proj (Term.app `o.basis_right_angle_rotation [`a `ha]) "." `ext)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.app `o.basis_right_angle_rotation [`a `ha])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `ha
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `a
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `o.basis_right_angle_rotation
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.app `o.basis_right_angle_rotation [`a `ha])
     ")")
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (tactic__
       (cdotTk (patternIgnore (token.«· » "·")))
       [(Tactic.simp "simp" [] [] [] ["[" [(Tactic.simpLemma [] [] `ha)] "]"] [])])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.simp "simp" [] [] [] ["[" [(Tactic.simpLemma [] [] `ha)] "]"] [])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `ha
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Classical.«tacticBy_cases_:_» "by_cases" [`ha ":"] («term_=_» `a "=" (num "0")))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_=_» `a "=" (num "0"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (num "0")
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 50, term))
      `a
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1024, (none, [anonymous]) <=? (some 50, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 50, (some 51, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, tactic) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
      («term_=_»
       («term_+_»
        (Algebra.Group.Defs.«term_•_»
         (RealInnerProductSpace.Analysis.InnerProductSpace.Basic.inner.real "⟪" `a ", " `x "⟫")
         " • "
         (Term.app
          (Term.explicit "@" `innerₛₗ)
          [(Data.Real.Basic.termℝ "ℝ") (Term.hole "_") (Term.hole "_") (Term.hole "_") `a]))
        "+"
        (Algebra.Group.Defs.«term_•_»
         (Term.app (Orientation.Analysis.InnerProductSpace.TwoDim.termω "ω") [`a `x])
         " • "
         (Term.app (Orientation.Analysis.InnerProductSpace.TwoDim.termω "ω") [`a])))
       "="
       (Algebra.Group.Defs.«term_•_»
        («term_^_» (Analysis.Normed.Group.Basic.«term‖_‖» "‖" `a "‖") "^" (num "2"))
        " • "
        (Term.app
         (Term.explicit "@" `innerₛₗ)
         [(Data.Real.Basic.termℝ "ℝ") (Term.hole "_") (Term.hole "_") (Term.hole "_") `x])))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Algebra.Group.Defs.«term_•_»
       («term_^_» (Analysis.Normed.Group.Basic.«term‖_‖» "‖" `a "‖") "^" (num "2"))
       " • "
       (Term.app
        (Term.explicit "@" `innerₛₗ)
        [(Data.Real.Basic.termℝ "ℝ") (Term.hole "_") (Term.hole "_") (Term.hole "_") `x]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       (Term.explicit "@" `innerₛₗ)
       [(Data.Real.Basic.termℝ "ℝ") (Term.hole "_") (Term.hole "_") (Term.hole "_") `x])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `x
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
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, term))
      (Term.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1023, term)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Data.Real.Basic.termℝ', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Data.Real.Basic.termℝ', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, term))
      (Data.Real.Basic.termℝ "ℝ")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1023, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (Term.explicit "@" `innerₛₗ)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `innerₛₗ
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (some 1024,
     term) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 73 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 73, term))
      («term_^_» (Analysis.Normed.Group.Basic.«term‖_‖» "‖" `a "‖") "^" (num "2"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (num "2")
[PrettyPrinter.parenthesize] ...precedences are 80 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 80, term))
      (Analysis.Normed.Group.Basic.«term‖_‖» "‖" `a "‖")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `a
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 81 >? 1024, (none, [anonymous]) <=? (some 80, term)
[PrettyPrinter.parenthesize] ...precedences are 74 >? 80, (some 80, term) <=? (some 73, term)
[PrettyPrinter.parenthesize] ...precedences are 51 >? 73, (some 73, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 50, term))
      («term_+_»
       (Algebra.Group.Defs.«term_•_»
        (RealInnerProductSpace.Analysis.InnerProductSpace.Basic.inner.real "⟪" `a ", " `x "⟫")
        " • "
        (Term.app
         (Term.explicit "@" `innerₛₗ)
         [(Data.Real.Basic.termℝ "ℝ") (Term.hole "_") (Term.hole "_") (Term.hole "_") `a]))
       "+"
       (Algebra.Group.Defs.«term_•_»
        (Term.app (Orientation.Analysis.InnerProductSpace.TwoDim.termω "ω") [`a `x])
        " • "
        (Term.app (Orientation.Analysis.InnerProductSpace.TwoDim.termω "ω") [`a])))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Algebra.Group.Defs.«term_•_»
       (Term.app (Orientation.Analysis.InnerProductSpace.TwoDim.termω "ω") [`a `x])
       " • "
       (Term.app (Orientation.Analysis.InnerProductSpace.TwoDim.termω "ω") [`a]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app (Orientation.Analysis.InnerProductSpace.TwoDim.termω "ω") [`a])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `a
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (Orientation.Analysis.InnerProductSpace.TwoDim.termω "ω")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Orientation.Analysis.InnerProductSpace.TwoDim.termω', expected 'Orientation.Analysis.InnerProductSpace.TwoDim.termω._@.Analysis.InnerProductSpace.TwoDim._hyg.7'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.opaque'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.instance'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.axiom'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.example'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.inductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.classInductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.structure'-/-- failed to format: format: uncaught backtrack exception
/--
    For vectors `a x y : E`, the identity `⟪a, x⟫ * ⟪a, y⟫ + ω a x * ω a y = ‖a‖ ^ 2 * ⟪x, y⟫`. (See
    `orientation.inner_mul_inner_add_area_form_mul_area_form` for the "applied" form.)-/
  theorem
    inner_mul_inner_add_area_form_mul_area_form'
    ( a x : E ) : ⟪ a , x ⟫ • @ innerₛₗ ℝ _ _ _ a + ω a x • ω a = ‖ a ‖ ^ 2 • @ innerₛₗ ℝ _ _ _ x
    :=
      by
        by_cases ha : a = 0
          · simp [ ha ]
          apply o.basis_right_angle_rotation a ha . ext
          intro i
          fin_cases i
          ·
            simp
                only
                [
                  real_inner_self_eq_norm_sq
                    ,
                    Algebra.id.smul_eq_mul
                    ,
                    innerₛₗ_apply
                    ,
                    LinearMap.smul_apply
                    ,
                    LinearMap.add_apply
                    ,
                    Matrix.cons_val_zero
                    ,
                    o.coe_basis_right_angle_rotation
                    ,
                    o.area_form_apply_self
                    ,
                    real_inner_comm
                  ]
              ring
          ·
            simp
                only
                [
                  real_inner_self_eq_norm_sq
                    ,
                    Algebra.id.smul_eq_mul
                    ,
                    innerₛₗ_apply
                    ,
                    LinearMap.smul_apply
                    ,
                    neg_inj
                    ,
                    LinearMap.add_apply
                    ,
                    Matrix.cons_val_one
                    ,
                    Matrix.head_cons
                    ,
                    o.coe_basis_right_angle_rotation
                    ,
                    o.area_form_right_angle_rotation_right
                    ,
                    o.area_form_apply_self
                    ,
                    o.inner_right_angle_rotation_right
                  ]
              rw [ o.area_form_swap ]
              ring
#align
  orientation.inner_mul_inner_add_area_form_mul_area_form' Orientation.inner_mul_inner_add_area_form_mul_area_form'

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers
      [(Command.docComment
        "/--"
        "For vectors `a x y : E`, the identity `⟪a, x⟫ * ⟪a, y⟫ + ω a x * ω a y = ‖a‖ ^ 2 * ⟪x, y⟫`. -/")]
      []
      []
      []
      []
      [])
     (Command.theorem
      "theorem"
      (Command.declId `inner_mul_inner_add_area_form_mul_area_form [])
      (Command.declSig
       [(Term.explicitBinder "(" [`a `x `y] [":" `E] [] ")")]
       (Term.typeSpec
        ":"
        («term_=_»
         («term_+_»
          («term_*_»
           (RealInnerProductSpace.Analysis.InnerProductSpace.Basic.inner.real "⟪" `a ", " `x "⟫")
           "*"
           (RealInnerProductSpace.Analysis.InnerProductSpace.Basic.inner.real "⟪" `a ", " `y "⟫"))
          "+"
          («term_*_»
           (Term.app (Orientation.Analysis.InnerProductSpace.TwoDim.termω "ω") [`a `x])
           "*"
           (Term.app (Orientation.Analysis.InnerProductSpace.TwoDim.termω "ω") [`a `y])))
         "="
         («term_*_»
          («term_^_» (Analysis.Normed.Group.Basic.«term‖_‖» "‖" `a "‖") "^" (num "2"))
          "*"
          (RealInnerProductSpace.Analysis.InnerProductSpace.Basic.inner.real "⟪" `x ", " `y "⟫")))))
      (Command.declValSimple
       ":="
       (Term.app
        `congr_arg
        [(Term.fun
          "fun"
          (Term.basicFun
           [`f]
           [(Term.typeSpec
             ":"
             (Algebra.Module.LinearMap.«term_→ₗ[_]_»
              `E
              " →ₗ["
              (Data.Real.Basic.termℝ "ℝ")
              "] "
              (Data.Real.Basic.termℝ "ℝ")))]
           "=>"
           (Term.app `f [`y])))
         (Term.app (Term.proj `o "." `inner_mul_inner_add_area_form_mul_area_form') [`a `x])])
       [])
      []
      []))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.abbrev'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.def'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       `congr_arg
       [(Term.fun
         "fun"
         (Term.basicFun
          [`f]
          [(Term.typeSpec
            ":"
            (Algebra.Module.LinearMap.«term_→ₗ[_]_»
             `E
             " →ₗ["
             (Data.Real.Basic.termℝ "ℝ")
             "] "
             (Data.Real.Basic.termℝ "ℝ")))]
          "=>"
          (Term.app `f [`y])))
        (Term.app (Term.proj `o "." `inner_mul_inner_add_area_form_mul_area_form') [`a `x])])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app (Term.proj `o "." `inner_mul_inner_add_area_form_mul_area_form') [`a `x])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `x
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `a
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (Term.proj `o "." `inner_mul_inner_add_area_form_mul_area_form')
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `o
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.app (Term.proj `o "." `inner_mul_inner_add_area_form_mul_area_form') [`a `x])
     ")")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.fun
       "fun"
       (Term.basicFun
        [`f]
        [(Term.typeSpec
          ":"
          (Algebra.Module.LinearMap.«term_→ₗ[_]_»
           `E
           " →ₗ["
           (Data.Real.Basic.termℝ "ℝ")
           "] "
           (Data.Real.Basic.termℝ "ℝ")))]
        "=>"
        (Term.app `f [`y])))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `f [`y])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `y
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `f
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Algebra.Module.LinearMap.«term_→ₗ[_]_»
       `E
       " →ₗ["
       (Data.Real.Basic.termℝ "ℝ")
       "] "
       (Data.Real.Basic.termℝ "ℝ"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Data.Real.Basic.termℝ "ℝ")
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Data.Real.Basic.termℝ "ℝ")
[PrettyPrinter.parenthesize] ...precedences are 25 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 25, term))
      `E
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 25, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 25, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.strictImplicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.implicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.instBinder'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
      `f
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1023, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (some 0, term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.fun
      "fun"
      (Term.basicFun
       [`f]
       [(Term.typeSpec
         ":"
         (Algebra.Module.LinearMap.«term_→ₗ[_]_»
          `E
          " →ₗ["
          (Data.Real.Basic.termℝ "ℝ")
          "] "
          (Data.Real.Basic.termℝ "ℝ")))]
       "=>"
       (Term.app `f [`y])))
     ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `congr_arg
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
      («term_=_»
       («term_+_»
        («term_*_»
         (RealInnerProductSpace.Analysis.InnerProductSpace.Basic.inner.real "⟪" `a ", " `x "⟫")
         "*"
         (RealInnerProductSpace.Analysis.InnerProductSpace.Basic.inner.real "⟪" `a ", " `y "⟫"))
        "+"
        («term_*_»
         (Term.app (Orientation.Analysis.InnerProductSpace.TwoDim.termω "ω") [`a `x])
         "*"
         (Term.app (Orientation.Analysis.InnerProductSpace.TwoDim.termω "ω") [`a `y])))
       "="
       («term_*_»
        («term_^_» (Analysis.Normed.Group.Basic.«term‖_‖» "‖" `a "‖") "^" (num "2"))
        "*"
        (RealInnerProductSpace.Analysis.InnerProductSpace.Basic.inner.real "⟪" `x ", " `y "⟫")))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_*_»
       («term_^_» (Analysis.Normed.Group.Basic.«term‖_‖» "‖" `a "‖") "^" (num "2"))
       "*"
       (RealInnerProductSpace.Analysis.InnerProductSpace.Basic.inner.real "⟪" `x ", " `y "⟫"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (RealInnerProductSpace.Analysis.InnerProductSpace.Basic.inner.real "⟪" `x ", " `y "⟫")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `y
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `x
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 71 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 70, term))
      («term_^_» (Analysis.Normed.Group.Basic.«term‖_‖» "‖" `a "‖") "^" (num "2"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (num "2")
[PrettyPrinter.parenthesize] ...precedences are 80 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 80, term))
      (Analysis.Normed.Group.Basic.«term‖_‖» "‖" `a "‖")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `a
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 81 >? 1024, (none, [anonymous]) <=? (some 80, term)
[PrettyPrinter.parenthesize] ...precedences are 70 >? 80, (some 80, term) <=? (some 70, term)
[PrettyPrinter.parenthesize] ...precedences are 51 >? 70, (some 71, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 50, term))
      («term_+_»
       («term_*_»
        (RealInnerProductSpace.Analysis.InnerProductSpace.Basic.inner.real "⟪" `a ", " `x "⟫")
        "*"
        (RealInnerProductSpace.Analysis.InnerProductSpace.Basic.inner.real "⟪" `a ", " `y "⟫"))
       "+"
       («term_*_»
        (Term.app (Orientation.Analysis.InnerProductSpace.TwoDim.termω "ω") [`a `x])
        "*"
        (Term.app (Orientation.Analysis.InnerProductSpace.TwoDim.termω "ω") [`a `y])))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_*_»
       (Term.app (Orientation.Analysis.InnerProductSpace.TwoDim.termω "ω") [`a `x])
       "*"
       (Term.app (Orientation.Analysis.InnerProductSpace.TwoDim.termω "ω") [`a `y]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app (Orientation.Analysis.InnerProductSpace.TwoDim.termω "ω") [`a `y])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `y
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `a
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (Orientation.Analysis.InnerProductSpace.TwoDim.termω "ω")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Orientation.Analysis.InnerProductSpace.TwoDim.termω', expected 'Orientation.Analysis.InnerProductSpace.TwoDim.termω._@.Analysis.InnerProductSpace.TwoDim._hyg.7'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.opaque'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.instance'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.axiom'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.example'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.inductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.classInductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.structure'-/-- failed to format: format: uncaught backtrack exception
/-- For vectors `a x y : E`, the identity `⟪a, x⟫ * ⟪a, y⟫ + ω a x * ω a y = ‖a‖ ^ 2 * ⟪x, y⟫`. -/
  theorem
    inner_mul_inner_add_area_form_mul_area_form
    ( a x y : E ) : ⟪ a , x ⟫ * ⟪ a , y ⟫ + ω a x * ω a y = ‖ a ‖ ^ 2 * ⟪ x , y ⟫
    := congr_arg fun f : E →ₗ[ ℝ ] ℝ => f y o . inner_mul_inner_add_area_form_mul_area_form' a x
#align
  orientation.inner_mul_inner_add_area_form_mul_area_form Orientation.inner_mul_inner_add_area_form_mul_area_form

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers [] [] [] [] [] [])
     (Command.theorem
      "theorem"
      (Command.declId `inner_sq_add_area_form_sq [])
      (Command.declSig
       [(Term.explicitBinder "(" [`a `b] [":" `E] [] ")")]
       (Term.typeSpec
        ":"
        («term_=_»
         («term_+_»
          («term_^_»
           (RealInnerProductSpace.Analysis.InnerProductSpace.Basic.inner.real "⟪" `a ", " `b "⟫")
           "^"
           (num "2"))
          "+"
          («term_^_»
           (Term.app (Orientation.Analysis.InnerProductSpace.TwoDim.termω "ω") [`a `b])
           "^"
           (num "2")))
         "="
         («term_*_»
          («term_^_» (Analysis.Normed.Group.Basic.«term‖_‖» "‖" `a "‖") "^" (num "2"))
          "*"
          («term_^_» (Analysis.Normed.Group.Basic.«term‖_‖» "‖" `b "‖") "^" (num "2"))))))
      (Command.declValSimple
       ":="
       (Term.byTactic
        "by"
        (Tactic.tacticSeq
         (Tactic.tacticSeq1Indented
          [(Std.Tactic.Simpa.simpa
            "simpa"
            []
            []
            (Std.Tactic.Simpa.simpaArgsRest
             []
             []
             []
             [(Tactic.simpArgs
               "["
               [(Tactic.simpLemma [] [] `sq)
                ","
                (Tactic.simpLemma [] [] `real_inner_self_eq_norm_sq)]
               "]")]
             ["using" (Term.app `o.inner_mul_inner_add_area_form_mul_area_form [`a `b `b])]))])))
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
         [(Std.Tactic.Simpa.simpa
           "simpa"
           []
           []
           (Std.Tactic.Simpa.simpaArgsRest
            []
            []
            []
            [(Tactic.simpArgs
              "["
              [(Tactic.simpLemma [] [] `sq)
               ","
               (Tactic.simpLemma [] [] `real_inner_self_eq_norm_sq)]
              "]")]
            ["using" (Term.app `o.inner_mul_inner_add_area_form_mul_area_form [`a `b `b])]))])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Std.Tactic.Simpa.simpa
       "simpa"
       []
       []
       (Std.Tactic.Simpa.simpaArgsRest
        []
        []
        []
        [(Tactic.simpArgs
          "["
          [(Tactic.simpLemma [] [] `sq) "," (Tactic.simpLemma [] [] `real_inner_self_eq_norm_sq)]
          "]")]
        ["using" (Term.app `o.inner_mul_inner_add_area_form_mul_area_form [`a `b `b])]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `o.inner_mul_inner_add_area_form_mul_area_form [`a `b `b])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `b
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `b
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `a
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `o.inner_mul_inner_add_area_form_mul_area_form
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `real_inner_self_eq_norm_sq
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `sq
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, tactic) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
      («term_=_»
       («term_+_»
        («term_^_»
         (RealInnerProductSpace.Analysis.InnerProductSpace.Basic.inner.real "⟪" `a ", " `b "⟫")
         "^"
         (num "2"))
        "+"
        («term_^_»
         (Term.app (Orientation.Analysis.InnerProductSpace.TwoDim.termω "ω") [`a `b])
         "^"
         (num "2")))
       "="
       («term_*_»
        («term_^_» (Analysis.Normed.Group.Basic.«term‖_‖» "‖" `a "‖") "^" (num "2"))
        "*"
        («term_^_» (Analysis.Normed.Group.Basic.«term‖_‖» "‖" `b "‖") "^" (num "2"))))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_*_»
       («term_^_» (Analysis.Normed.Group.Basic.«term‖_‖» "‖" `a "‖") "^" (num "2"))
       "*"
       («term_^_» (Analysis.Normed.Group.Basic.«term‖_‖» "‖" `b "‖") "^" (num "2")))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_^_» (Analysis.Normed.Group.Basic.«term‖_‖» "‖" `b "‖") "^" (num "2"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (num "2")
[PrettyPrinter.parenthesize] ...precedences are 80 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 80, term))
      (Analysis.Normed.Group.Basic.«term‖_‖» "‖" `b "‖")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `b
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 81 >? 1024, (none, [anonymous]) <=? (some 80, term)
[PrettyPrinter.parenthesize] ...precedences are 71 >? 80, (some 80, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 70, term))
      («term_^_» (Analysis.Normed.Group.Basic.«term‖_‖» "‖" `a "‖") "^" (num "2"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (num "2")
[PrettyPrinter.parenthesize] ...precedences are 80 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 80, term))
      (Analysis.Normed.Group.Basic.«term‖_‖» "‖" `a "‖")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `a
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 81 >? 1024, (none, [anonymous]) <=? (some 80, term)
[PrettyPrinter.parenthesize] ...precedences are 70 >? 80, (some 80, term) <=? (some 70, term)
[PrettyPrinter.parenthesize] ...precedences are 51 >? 70, (some 71, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 50, term))
      («term_+_»
       («term_^_»
        (RealInnerProductSpace.Analysis.InnerProductSpace.Basic.inner.real "⟪" `a ", " `b "⟫")
        "^"
        (num "2"))
       "+"
       («term_^_»
        (Term.app (Orientation.Analysis.InnerProductSpace.TwoDim.termω "ω") [`a `b])
        "^"
        (num "2")))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_^_»
       (Term.app (Orientation.Analysis.InnerProductSpace.TwoDim.termω "ω") [`a `b])
       "^"
       (num "2"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (num "2")
[PrettyPrinter.parenthesize] ...precedences are 80 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 80, term))
      (Term.app (Orientation.Analysis.InnerProductSpace.TwoDim.termω "ω") [`a `b])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `b
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `a
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (Orientation.Analysis.InnerProductSpace.TwoDim.termω "ω")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Orientation.Analysis.InnerProductSpace.TwoDim.termω', expected 'Orientation.Analysis.InnerProductSpace.TwoDim.termω._@.Analysis.InnerProductSpace.TwoDim._hyg.7'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.opaque'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.instance'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.axiom'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.example'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.inductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.classInductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.structure'-/-- failed to format: format: uncaught backtrack exception
theorem
  inner_sq_add_area_form_sq
  ( a b : E ) : ⟪ a , b ⟫ ^ 2 + ω a b ^ 2 = ‖ a ‖ ^ 2 * ‖ b ‖ ^ 2
  :=
    by
      simpa
        [ sq , real_inner_self_eq_norm_sq ]
          using o.inner_mul_inner_add_area_form_mul_area_form a b b
#align orientation.inner_sq_add_area_form_sq Orientation.inner_sq_add_area_form_sq

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers
      [(Command.docComment
        "/--"
        "For vectors `a x y : E`, the identity `⟪a, x⟫ * ω a y - ω a x * ⟪a, y⟫ = ‖a‖ ^ 2 * ω x y`. (See\n`orientation.inner_mul_area_form_sub` for the \"applied\" form.) -/")]
      []
      []
      []
      []
      [])
     (Command.theorem
      "theorem"
      (Command.declId `inner_mul_area_form_sub' [])
      (Command.declSig
       [(Term.explicitBinder "(" [`a `x] [":" `E] [] ")")]
       (Term.typeSpec
        ":"
        («term_=_»
         («term_-_»
          (Algebra.Group.Defs.«term_•_»
           (RealInnerProductSpace.Analysis.InnerProductSpace.Basic.inner.real "⟪" `a ", " `x "⟫")
           " • "
           (Term.app (Orientation.Analysis.InnerProductSpace.TwoDim.termω "ω") [`a]))
          "-"
          (Algebra.Group.Defs.«term_•_»
           (Term.app (Orientation.Analysis.InnerProductSpace.TwoDim.termω "ω") [`a `x])
           " • "
           (Term.app
            (Term.explicit "@" `innerₛₗ)
            [(Data.Real.Basic.termℝ "ℝ") (Term.hole "_") (Term.hole "_") (Term.hole "_") `a])))
         "="
         (Algebra.Group.Defs.«term_•_»
          («term_^_» (Analysis.Normed.Group.Basic.«term‖_‖» "‖" `a "‖") "^" (num "2"))
          " • "
          (Term.app (Orientation.Analysis.InnerProductSpace.TwoDim.termω "ω") [`x])))))
      (Command.declValSimple
       ":="
       (Term.byTactic
        "by"
        (Tactic.tacticSeq
         (Tactic.tacticSeq1Indented
          [(Classical.«tacticBy_cases_:_» "by_cases" [`ha ":"] («term_=_» `a "=" (num "0")))
           []
           (tactic__
            (cdotTk (patternIgnore (token.«· » "·")))
            [(Tactic.simp "simp" [] [] [] ["[" [(Tactic.simpLemma [] [] `ha)] "]"] [])])
           []
           (Tactic.apply
            "apply"
            (Term.proj (Term.app `o.basis_right_angle_rotation [`a `ha]) "." `ext))
           []
           (Tactic.intro "intro" [`i])
           []
           (Lean.Elab.Tactic.finCases "fin_cases" [`i] [])
           []
           (tactic__
            (cdotTk (patternIgnore (token.«· » "·")))
            [(Tactic.simp
              "simp"
              []
              []
              ["only"]
              ["["
               [(Tactic.simpLemma [] [] `o.coe_basis_right_angle_rotation)
                ","
                (Tactic.simpLemma [] [] `o.area_form_apply_self)
                ","
                (Tactic.simpLemma [] [] (Term.app `o.area_form_swap [`a `x]))
                ","
                (Tactic.simpLemma [] [] `real_inner_self_eq_norm_sq)
                ","
                (Tactic.simpLemma [] [] `Algebra.id.smul_eq_mul)
                ","
                (Tactic.simpLemma [] [] `innerₛₗ_apply)
                ","
                (Tactic.simpLemma [] [] `LinearMap.sub_apply)
                ","
                (Tactic.simpLemma [] [] `LinearMap.smul_apply)
                ","
                (Tactic.simpLemma [] [] `Matrix.cons_val_zero)]
               "]"]
              [])
             []
             (Mathlib.Tactic.RingNF.ring "ring")])
           []
           (tactic__
            (cdotTk (patternIgnore (token.«· » "·")))
            [(Tactic.simp
              "simp"
              []
              []
              ["only"]
              ["["
               [(Tactic.simpLemma [] [] `o.area_form_right_angle_rotation_right)
                ","
                (Tactic.simpLemma [] [] `o.area_form_apply_self)
                ","
                (Tactic.simpLemma [] [] `o.coe_basis_right_angle_rotation)
                ","
                (Tactic.simpLemma [] [] `o.inner_right_angle_rotation_right)
                ","
                (Tactic.simpLemma [] [] `real_inner_self_eq_norm_sq)
                ","
                (Tactic.simpLemma [] [] `real_inner_comm)
                ","
                (Tactic.simpLemma [] [] `Algebra.id.smul_eq_mul)
                ","
                (Tactic.simpLemma [] [] `innerₛₗ_apply)
                ","
                (Tactic.simpLemma [] [] `LinearMap.smul_apply)
                ","
                (Tactic.simpLemma [] [] `LinearMap.sub_apply)
                ","
                (Tactic.simpLemma [] [] `Matrix.cons_val_one)
                ","
                (Tactic.simpLemma [] [] `Matrix.head_cons)]
               "]"]
              [])
             []
             (Mathlib.Tactic.RingNF.ring "ring")])])))
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
         [(Classical.«tacticBy_cases_:_» "by_cases" [`ha ":"] («term_=_» `a "=" (num "0")))
          []
          (tactic__
           (cdotTk (patternIgnore (token.«· » "·")))
           [(Tactic.simp "simp" [] [] [] ["[" [(Tactic.simpLemma [] [] `ha)] "]"] [])])
          []
          (Tactic.apply
           "apply"
           (Term.proj (Term.app `o.basis_right_angle_rotation [`a `ha]) "." `ext))
          []
          (Tactic.intro "intro" [`i])
          []
          (Lean.Elab.Tactic.finCases "fin_cases" [`i] [])
          []
          (tactic__
           (cdotTk (patternIgnore (token.«· » "·")))
           [(Tactic.simp
             "simp"
             []
             []
             ["only"]
             ["["
              [(Tactic.simpLemma [] [] `o.coe_basis_right_angle_rotation)
               ","
               (Tactic.simpLemma [] [] `o.area_form_apply_self)
               ","
               (Tactic.simpLemma [] [] (Term.app `o.area_form_swap [`a `x]))
               ","
               (Tactic.simpLemma [] [] `real_inner_self_eq_norm_sq)
               ","
               (Tactic.simpLemma [] [] `Algebra.id.smul_eq_mul)
               ","
               (Tactic.simpLemma [] [] `innerₛₗ_apply)
               ","
               (Tactic.simpLemma [] [] `LinearMap.sub_apply)
               ","
               (Tactic.simpLemma [] [] `LinearMap.smul_apply)
               ","
               (Tactic.simpLemma [] [] `Matrix.cons_val_zero)]
              "]"]
             [])
            []
            (Mathlib.Tactic.RingNF.ring "ring")])
          []
          (tactic__
           (cdotTk (patternIgnore (token.«· » "·")))
           [(Tactic.simp
             "simp"
             []
             []
             ["only"]
             ["["
              [(Tactic.simpLemma [] [] `o.area_form_right_angle_rotation_right)
               ","
               (Tactic.simpLemma [] [] `o.area_form_apply_self)
               ","
               (Tactic.simpLemma [] [] `o.coe_basis_right_angle_rotation)
               ","
               (Tactic.simpLemma [] [] `o.inner_right_angle_rotation_right)
               ","
               (Tactic.simpLemma [] [] `real_inner_self_eq_norm_sq)
               ","
               (Tactic.simpLemma [] [] `real_inner_comm)
               ","
               (Tactic.simpLemma [] [] `Algebra.id.smul_eq_mul)
               ","
               (Tactic.simpLemma [] [] `innerₛₗ_apply)
               ","
               (Tactic.simpLemma [] [] `LinearMap.smul_apply)
               ","
               (Tactic.simpLemma [] [] `LinearMap.sub_apply)
               ","
               (Tactic.simpLemma [] [] `Matrix.cons_val_one)
               ","
               (Tactic.simpLemma [] [] `Matrix.head_cons)]
              "]"]
             [])
            []
            (Mathlib.Tactic.RingNF.ring "ring")])])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (tactic__
       (cdotTk (patternIgnore (token.«· » "·")))
       [(Tactic.simp
         "simp"
         []
         []
         ["only"]
         ["["
          [(Tactic.simpLemma [] [] `o.area_form_right_angle_rotation_right)
           ","
           (Tactic.simpLemma [] [] `o.area_form_apply_self)
           ","
           (Tactic.simpLemma [] [] `o.coe_basis_right_angle_rotation)
           ","
           (Tactic.simpLemma [] [] `o.inner_right_angle_rotation_right)
           ","
           (Tactic.simpLemma [] [] `real_inner_self_eq_norm_sq)
           ","
           (Tactic.simpLemma [] [] `real_inner_comm)
           ","
           (Tactic.simpLemma [] [] `Algebra.id.smul_eq_mul)
           ","
           (Tactic.simpLemma [] [] `innerₛₗ_apply)
           ","
           (Tactic.simpLemma [] [] `LinearMap.smul_apply)
           ","
           (Tactic.simpLemma [] [] `LinearMap.sub_apply)
           ","
           (Tactic.simpLemma [] [] `Matrix.cons_val_one)
           ","
           (Tactic.simpLemma [] [] `Matrix.head_cons)]
          "]"]
         [])
        []
        (Mathlib.Tactic.RingNF.ring "ring")])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Mathlib.Tactic.RingNF.ring "ring")
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.simp
       "simp"
       []
       []
       ["only"]
       ["["
        [(Tactic.simpLemma [] [] `o.area_form_right_angle_rotation_right)
         ","
         (Tactic.simpLemma [] [] `o.area_form_apply_self)
         ","
         (Tactic.simpLemma [] [] `o.coe_basis_right_angle_rotation)
         ","
         (Tactic.simpLemma [] [] `o.inner_right_angle_rotation_right)
         ","
         (Tactic.simpLemma [] [] `real_inner_self_eq_norm_sq)
         ","
         (Tactic.simpLemma [] [] `real_inner_comm)
         ","
         (Tactic.simpLemma [] [] `Algebra.id.smul_eq_mul)
         ","
         (Tactic.simpLemma [] [] `innerₛₗ_apply)
         ","
         (Tactic.simpLemma [] [] `LinearMap.smul_apply)
         ","
         (Tactic.simpLemma [] [] `LinearMap.sub_apply)
         ","
         (Tactic.simpLemma [] [] `Matrix.cons_val_one)
         ","
         (Tactic.simpLemma [] [] `Matrix.head_cons)]
        "]"]
       [])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `Matrix.head_cons
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `Matrix.cons_val_one
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `LinearMap.sub_apply
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `LinearMap.smul_apply
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `innerₛₗ_apply
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `Algebra.id.smul_eq_mul
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `real_inner_comm
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `real_inner_self_eq_norm_sq
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `o.inner_right_angle_rotation_right
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `o.coe_basis_right_angle_rotation
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `o.area_form_apply_self
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `o.area_form_right_angle_rotation_right
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (tactic__
       (cdotTk (patternIgnore (token.«· » "·")))
       [(Tactic.simp
         "simp"
         []
         []
         ["only"]
         ["["
          [(Tactic.simpLemma [] [] `o.coe_basis_right_angle_rotation)
           ","
           (Tactic.simpLemma [] [] `o.area_form_apply_self)
           ","
           (Tactic.simpLemma [] [] (Term.app `o.area_form_swap [`a `x]))
           ","
           (Tactic.simpLemma [] [] `real_inner_self_eq_norm_sq)
           ","
           (Tactic.simpLemma [] [] `Algebra.id.smul_eq_mul)
           ","
           (Tactic.simpLemma [] [] `innerₛₗ_apply)
           ","
           (Tactic.simpLemma [] [] `LinearMap.sub_apply)
           ","
           (Tactic.simpLemma [] [] `LinearMap.smul_apply)
           ","
           (Tactic.simpLemma [] [] `Matrix.cons_val_zero)]
          "]"]
         [])
        []
        (Mathlib.Tactic.RingNF.ring "ring")])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Mathlib.Tactic.RingNF.ring "ring")
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.simp
       "simp"
       []
       []
       ["only"]
       ["["
        [(Tactic.simpLemma [] [] `o.coe_basis_right_angle_rotation)
         ","
         (Tactic.simpLemma [] [] `o.area_form_apply_self)
         ","
         (Tactic.simpLemma [] [] (Term.app `o.area_form_swap [`a `x]))
         ","
         (Tactic.simpLemma [] [] `real_inner_self_eq_norm_sq)
         ","
         (Tactic.simpLemma [] [] `Algebra.id.smul_eq_mul)
         ","
         (Tactic.simpLemma [] [] `innerₛₗ_apply)
         ","
         (Tactic.simpLemma [] [] `LinearMap.sub_apply)
         ","
         (Tactic.simpLemma [] [] `LinearMap.smul_apply)
         ","
         (Tactic.simpLemma [] [] `Matrix.cons_val_zero)]
        "]"]
       [])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `Matrix.cons_val_zero
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `LinearMap.smul_apply
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `LinearMap.sub_apply
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `innerₛₗ_apply
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `Algebra.id.smul_eq_mul
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `real_inner_self_eq_norm_sq
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `o.area_form_swap [`a `x])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `x
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `a
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `o.area_form_swap
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `o.area_form_apply_self
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `o.coe_basis_right_angle_rotation
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Lean.Elab.Tactic.finCases "fin_cases" [`i] [])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'null', expected 'token.«*»'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `i
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.intro "intro" [`i])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `i
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.apply "apply" (Term.proj (Term.app `o.basis_right_angle_rotation [`a `ha]) "." `ext))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.proj (Term.app `o.basis_right_angle_rotation [`a `ha]) "." `ext)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.app `o.basis_right_angle_rotation [`a `ha])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `ha
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `a
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `o.basis_right_angle_rotation
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.app `o.basis_right_angle_rotation [`a `ha])
     ")")
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (tactic__
       (cdotTk (patternIgnore (token.«· » "·")))
       [(Tactic.simp "simp" [] [] [] ["[" [(Tactic.simpLemma [] [] `ha)] "]"] [])])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.simp "simp" [] [] [] ["[" [(Tactic.simpLemma [] [] `ha)] "]"] [])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `ha
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Classical.«tacticBy_cases_:_» "by_cases" [`ha ":"] («term_=_» `a "=" (num "0")))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_=_» `a "=" (num "0"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (num "0")
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 50, term))
      `a
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1024, (none, [anonymous]) <=? (some 50, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 50, (some 51, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, tactic) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
      («term_=_»
       («term_-_»
        (Algebra.Group.Defs.«term_•_»
         (RealInnerProductSpace.Analysis.InnerProductSpace.Basic.inner.real "⟪" `a ", " `x "⟫")
         " • "
         (Term.app (Orientation.Analysis.InnerProductSpace.TwoDim.termω "ω") [`a]))
        "-"
        (Algebra.Group.Defs.«term_•_»
         (Term.app (Orientation.Analysis.InnerProductSpace.TwoDim.termω "ω") [`a `x])
         " • "
         (Term.app
          (Term.explicit "@" `innerₛₗ)
          [(Data.Real.Basic.termℝ "ℝ") (Term.hole "_") (Term.hole "_") (Term.hole "_") `a])))
       "="
       (Algebra.Group.Defs.«term_•_»
        («term_^_» (Analysis.Normed.Group.Basic.«term‖_‖» "‖" `a "‖") "^" (num "2"))
        " • "
        (Term.app (Orientation.Analysis.InnerProductSpace.TwoDim.termω "ω") [`x])))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Algebra.Group.Defs.«term_•_»
       («term_^_» (Analysis.Normed.Group.Basic.«term‖_‖» "‖" `a "‖") "^" (num "2"))
       " • "
       (Term.app (Orientation.Analysis.InnerProductSpace.TwoDim.termω "ω") [`x]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app (Orientation.Analysis.InnerProductSpace.TwoDim.termω "ω") [`x])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `x
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (Orientation.Analysis.InnerProductSpace.TwoDim.termω "ω")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Orientation.Analysis.InnerProductSpace.TwoDim.termω', expected 'Orientation.Analysis.InnerProductSpace.TwoDim.termω._@.Analysis.InnerProductSpace.TwoDim._hyg.7'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.opaque'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.instance'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.axiom'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.example'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.inductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.classInductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.structure'-/-- failed to format: format: uncaught backtrack exception
/--
    For vectors `a x y : E`, the identity `⟪a, x⟫ * ω a y - ω a x * ⟪a, y⟫ = ‖a‖ ^ 2 * ω x y`. (See
    `orientation.inner_mul_area_form_sub` for the "applied" form.) -/
  theorem
    inner_mul_area_form_sub'
    ( a x : E ) : ⟪ a , x ⟫ • ω a - ω a x • @ innerₛₗ ℝ _ _ _ a = ‖ a ‖ ^ 2 • ω x
    :=
      by
        by_cases ha : a = 0
          · simp [ ha ]
          apply o.basis_right_angle_rotation a ha . ext
          intro i
          fin_cases i
          ·
            simp
                only
                [
                  o.coe_basis_right_angle_rotation
                    ,
                    o.area_form_apply_self
                    ,
                    o.area_form_swap a x
                    ,
                    real_inner_self_eq_norm_sq
                    ,
                    Algebra.id.smul_eq_mul
                    ,
                    innerₛₗ_apply
                    ,
                    LinearMap.sub_apply
                    ,
                    LinearMap.smul_apply
                    ,
                    Matrix.cons_val_zero
                  ]
              ring
          ·
            simp
                only
                [
                  o.area_form_right_angle_rotation_right
                    ,
                    o.area_form_apply_self
                    ,
                    o.coe_basis_right_angle_rotation
                    ,
                    o.inner_right_angle_rotation_right
                    ,
                    real_inner_self_eq_norm_sq
                    ,
                    real_inner_comm
                    ,
                    Algebra.id.smul_eq_mul
                    ,
                    innerₛₗ_apply
                    ,
                    LinearMap.smul_apply
                    ,
                    LinearMap.sub_apply
                    ,
                    Matrix.cons_val_one
                    ,
                    Matrix.head_cons
                  ]
              ring
#align orientation.inner_mul_area_form_sub' Orientation.inner_mul_area_form_sub'

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers
      [(Command.docComment
        "/--"
        "For vectors `a x y : E`, the identity `⟪a, x⟫ * ω a y - ω a x * ⟪a, y⟫ = ‖a‖ ^ 2 * ω x y`. -/")]
      []
      []
      []
      []
      [])
     (Command.theorem
      "theorem"
      (Command.declId `inner_mul_area_form_sub [])
      (Command.declSig
       [(Term.explicitBinder "(" [`a `x `y] [":" `E] [] ")")]
       (Term.typeSpec
        ":"
        («term_=_»
         («term_-_»
          («term_*_»
           (RealInnerProductSpace.Analysis.InnerProductSpace.Basic.inner.real "⟪" `a ", " `x "⟫")
           "*"
           (Term.app (Orientation.Analysis.InnerProductSpace.TwoDim.termω "ω") [`a `y]))
          "-"
          («term_*_»
           (Term.app (Orientation.Analysis.InnerProductSpace.TwoDim.termω "ω") [`a `x])
           "*"
           (RealInnerProductSpace.Analysis.InnerProductSpace.Basic.inner.real "⟪" `a ", " `y "⟫")))
         "="
         («term_*_»
          («term_^_» (Analysis.Normed.Group.Basic.«term‖_‖» "‖" `a "‖") "^" (num "2"))
          "*"
          (Term.app (Orientation.Analysis.InnerProductSpace.TwoDim.termω "ω") [`x `y])))))
      (Command.declValSimple
       ":="
       (Term.app
        `congr_arg
        [(Term.fun
          "fun"
          (Term.basicFun
           [`f]
           [(Term.typeSpec
             ":"
             (Algebra.Module.LinearMap.«term_→ₗ[_]_»
              `E
              " →ₗ["
              (Data.Real.Basic.termℝ "ℝ")
              "] "
              (Data.Real.Basic.termℝ "ℝ")))]
           "=>"
           (Term.app `f [`y])))
         (Term.app (Term.proj `o "." `inner_mul_area_form_sub') [`a `x])])
       [])
      []
      []))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.abbrev'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.def'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       `congr_arg
       [(Term.fun
         "fun"
         (Term.basicFun
          [`f]
          [(Term.typeSpec
            ":"
            (Algebra.Module.LinearMap.«term_→ₗ[_]_»
             `E
             " →ₗ["
             (Data.Real.Basic.termℝ "ℝ")
             "] "
             (Data.Real.Basic.termℝ "ℝ")))]
          "=>"
          (Term.app `f [`y])))
        (Term.app (Term.proj `o "." `inner_mul_area_form_sub') [`a `x])])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app (Term.proj `o "." `inner_mul_area_form_sub') [`a `x])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `x
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `a
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (Term.proj `o "." `inner_mul_area_form_sub')
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `o
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.app (Term.proj `o "." `inner_mul_area_form_sub') [`a `x])
     ")")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.fun
       "fun"
       (Term.basicFun
        [`f]
        [(Term.typeSpec
          ":"
          (Algebra.Module.LinearMap.«term_→ₗ[_]_»
           `E
           " →ₗ["
           (Data.Real.Basic.termℝ "ℝ")
           "] "
           (Data.Real.Basic.termℝ "ℝ")))]
        "=>"
        (Term.app `f [`y])))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `f [`y])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `y
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `f
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Algebra.Module.LinearMap.«term_→ₗ[_]_»
       `E
       " →ₗ["
       (Data.Real.Basic.termℝ "ℝ")
       "] "
       (Data.Real.Basic.termℝ "ℝ"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Data.Real.Basic.termℝ "ℝ")
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Data.Real.Basic.termℝ "ℝ")
[PrettyPrinter.parenthesize] ...precedences are 25 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 25, term))
      `E
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 25, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 25, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.strictImplicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.implicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.instBinder'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
      `f
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1023, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (some 0, term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.fun
      "fun"
      (Term.basicFun
       [`f]
       [(Term.typeSpec
         ":"
         (Algebra.Module.LinearMap.«term_→ₗ[_]_»
          `E
          " →ₗ["
          (Data.Real.Basic.termℝ "ℝ")
          "] "
          (Data.Real.Basic.termℝ "ℝ")))]
       "=>"
       (Term.app `f [`y])))
     ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `congr_arg
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
      («term_=_»
       («term_-_»
        («term_*_»
         (RealInnerProductSpace.Analysis.InnerProductSpace.Basic.inner.real "⟪" `a ", " `x "⟫")
         "*"
         (Term.app (Orientation.Analysis.InnerProductSpace.TwoDim.termω "ω") [`a `y]))
        "-"
        («term_*_»
         (Term.app (Orientation.Analysis.InnerProductSpace.TwoDim.termω "ω") [`a `x])
         "*"
         (RealInnerProductSpace.Analysis.InnerProductSpace.Basic.inner.real "⟪" `a ", " `y "⟫")))
       "="
       («term_*_»
        («term_^_» (Analysis.Normed.Group.Basic.«term‖_‖» "‖" `a "‖") "^" (num "2"))
        "*"
        (Term.app (Orientation.Analysis.InnerProductSpace.TwoDim.termω "ω") [`x `y])))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_*_»
       («term_^_» (Analysis.Normed.Group.Basic.«term‖_‖» "‖" `a "‖") "^" (num "2"))
       "*"
       (Term.app (Orientation.Analysis.InnerProductSpace.TwoDim.termω "ω") [`x `y]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app (Orientation.Analysis.InnerProductSpace.TwoDim.termω "ω") [`x `y])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `y
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `x
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (Orientation.Analysis.InnerProductSpace.TwoDim.termω "ω")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Orientation.Analysis.InnerProductSpace.TwoDim.termω', expected 'Orientation.Analysis.InnerProductSpace.TwoDim.termω._@.Analysis.InnerProductSpace.TwoDim._hyg.7'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.opaque'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.instance'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.axiom'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.example'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.inductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.classInductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.structure'-/-- failed to format: format: uncaught backtrack exception
/-- For vectors `a x y : E`, the identity `⟪a, x⟫ * ω a y - ω a x * ⟪a, y⟫ = ‖a‖ ^ 2 * ω x y`. -/
  theorem
    inner_mul_area_form_sub
    ( a x y : E ) : ⟪ a , x ⟫ * ω a y - ω a x * ⟪ a , y ⟫ = ‖ a ‖ ^ 2 * ω x y
    := congr_arg fun f : E →ₗ[ ℝ ] ℝ => f y o . inner_mul_area_form_sub' a x
#align orientation.inner_mul_area_form_sub Orientation.inner_mul_area_form_sub

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers [] [] [] [] [] [])
     (Command.theorem
      "theorem"
      (Command.declId `nonneg_inner_and_area_form_eq_zero_iff_same_ray [])
      (Command.declSig
       [(Term.explicitBinder "(" [`x `y] [":" `E] [] ")")]
       (Term.typeSpec
        ":"
        («term_↔_»
         («term_∧_»
          («term_≤_»
           (num "0")
           "≤"
           (RealInnerProductSpace.Analysis.InnerProductSpace.Basic.inner.real "⟪" `x ", " `y "⟫"))
          "∧"
          («term_=_»
           (Term.app (Orientation.Analysis.InnerProductSpace.TwoDim.termω "ω") [`x `y])
           "="
           (num "0")))
         "↔"
         (Term.app `SameRay [(Data.Real.Basic.termℝ "ℝ") `x `y]))))
      (Command.declValSimple
       ":="
       (Term.byTactic
        "by"
        (Tactic.tacticSeq
         (Tactic.tacticSeq1Indented
          [(Classical.«tacticBy_cases_:_» "by_cases" [`hx ":"] («term_=_» `x "=" (num "0")))
           []
           (tactic__
            (cdotTk (patternIgnore (token.«· » "·")))
            [(Tactic.simp "simp" [] [] [] ["[" [(Tactic.simpLemma [] [] `hx)] "]"] [])])
           []
           (Tactic.constructor "constructor")
           []
           (tactic__
            (cdotTk (patternIgnore (token.«· » "·")))
            [(Tactic.tacticLet_
              "let"
              (Term.letDecl
               (Term.letIdDecl
                `a
                []
                [(Term.typeSpec ":" (Data.Real.Basic.termℝ "ℝ"))]
                ":="
                (Term.app
                 (Term.proj (Term.app `o.basis_right_angle_rotation [`x `hx]) "." `repr)
                 [`y (num "0")]))))
             []
             (Tactic.tacticLet_
              "let"
              (Term.letDecl
               (Term.letIdDecl
                `b
                []
                [(Term.typeSpec ":" (Data.Real.Basic.termℝ "ℝ"))]
                ":="
                (Term.app
                 (Term.proj (Term.app `o.basis_right_angle_rotation [`x `hx]) "." `repr)
                 [`y (num "1")]))))
             []
             (Tactic.tacticSuffices_
              "suffices"
              (Term.sufficesDecl
               []
               (Term.arrow
                («term_∧_»
                 («term_≤_»
                  (num "0")
                  "≤"
                  («term_*_»
                   `a
                   "*"
                   («term_^_» (Analysis.Normed.Group.Basic.«term‖_‖» "‖" `x "‖") "^" (num "2"))))
                 "∧"
                 («term_=_»
                  («term_*_»
                   `b
                   "*"
                   («term_^_» (Analysis.Normed.Group.Basic.«term‖_‖» "‖" `x "‖") "^" (num "2")))
                  "="
                  (num "0")))
                "→"
                (Term.app
                 `SameRay
                 [(Data.Real.Basic.termℝ "ℝ")
                  `x
                  («term_+_»
                   (Algebra.Group.Defs.«term_•_» `a " • " `x)
                   "+"
                   (Algebra.Group.Defs.«term_•_»
                    `b
                    " • "
                    (Term.app (Orientation.Analysis.InnerProductSpace.TwoDim.termJ "J") [`x])))]))
               (Term.byTactic'
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
                        (Term.proj (Term.app `o.basis_right_angle_rotation [`x `hx]) "." `sum_repr)
                        [`y]))]
                     "]")
                    [])
                   []
                   (Tactic.simp
                    "simp"
                    []
                    []
                    ["only"]
                    ["["
                     [(Tactic.simpLemma [] [] `Fin.sum_univ_succ)
                      ","
                      (Tactic.simpLemma [] [] `coe_basis_right_angle_rotation)]
                     "]"]
                    [])
                   []
                   (Tactic.dsimp "dsimp" [] [] [] [] [])
                   []
                   (Tactic.simp
                    "simp"
                    []
                    []
                    ["only"]
                    ["["
                     [(Tactic.simpLemma [] [] `o.area_form_apply_self)
                      ","
                      (Tactic.simpLemma [] [] `map_smul)
                      ","
                      (Tactic.simpLemma [] [] `map_add)
                      ","
                      (Tactic.simpLemma [] [] `map_zero)
                      ","
                      (Tactic.simpLemma [] [] `inner_smul_left)
                      ","
                      (Tactic.simpLemma [] [] `inner_smul_right)
                      ","
                      (Tactic.simpLemma [] [] `inner_add_left)
                      ","
                      (Tactic.simpLemma [] [] `inner_add_right)
                      ","
                      (Tactic.simpLemma [] [] `inner_zero_right)
                      ","
                      (Tactic.simpLemma [] [] `LinearMap.add_apply)
                      ","
                      (Tactic.simpLemma [] [] `Matrix.cons_val_one)]
                     "]"]
                    [])
                   []
                   (Tactic.dsimp "dsimp" [] [] [] [] [])
                   []
                   (Tactic.simp
                    "simp"
                    []
                    []
                    ["only"]
                    ["["
                     [(Tactic.simpLemma [] [] `o.area_form_right_angle_rotation_right)
                      ","
                      (Tactic.simpLemma [] [] `mul_zero)
                      ","
                      (Tactic.simpLemma [] [] `add_zero)
                      ","
                      (Tactic.simpLemma [] [] `zero_add)
                      ","
                      (Tactic.simpLemma [] [] `neg_zero)
                      ","
                      (Tactic.simpLemma [] [] `o.inner_right_angle_rotation_right)
                      ","
                      (Tactic.simpLemma [] [] `o.area_form_apply_self)
                      ","
                      (Tactic.simpLemma [] [] `real_inner_self_eq_norm_sq)]
                     "]"]
                    [])
                   []
                   (Tactic.exact "exact" `this)])))))
             []
             (Std.Tactic.rintro
              "rintro"
              [(Std.Tactic.RCases.rintroPat.one
                (Std.Tactic.RCases.rcasesPat.tuple
                 "⟨"
                 [(Std.Tactic.RCases.rcasesPatLo
                   (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `ha)])
                   [])
                  ","
                  (Std.Tactic.RCases.rcasesPatLo
                   (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `hb)])
                   [])]
                 "⟩"))]
              [])
             []
             (Tactic.tacticHave_
              "have"
              (Term.haveDecl
               (Term.haveIdDecl
                [`hx' []]
                [(Term.typeSpec
                  ":"
                  («term_<_» (num "0") "<" (Analysis.Normed.Group.Basic.«term‖_‖» "‖" `x "‖")))]
                ":="
                (Term.byTactic
                 "by"
                 (Tactic.tacticSeq
                  (Tactic.tacticSeq1Indented
                   [(Std.Tactic.Simpa.simpa
                     "simpa"
                     []
                     []
                     (Std.Tactic.Simpa.simpaArgsRest [] [] [] [] ["using" `hx]))]))))))
             []
             (Tactic.tacticHave_
              "have"
              (Term.haveDecl
               (Term.haveIdDecl
                [`ha' []]
                [(Term.typeSpec ":" («term_≤_» (num "0") "≤" `a))]
                ":="
                (Term.app
                 `nonneg_of_mul_nonneg_left
                 [`ha
                  (Term.byTactic
                   "by"
                   (Tactic.tacticSeq
                    (Tactic.tacticSeq1Indented
                     [(Mathlib.Tactic.Positivity.positivity "positivity")])))]))))
             []
             (Tactic.tacticHave_
              "have"
              (Term.haveDecl
               (Term.haveIdDecl
                [`hb' []]
                [(Term.typeSpec ":" («term_=_» `b "=" (num "0")))]
                ":="
                (Term.app
                 `eq_zero_of_ne_zero_of_mul_right_eq_zero
                 [(Term.app `pow_ne_zero [(num "2") `hx'.ne']) `hb]))))
             []
             (Std.Tactic.Simpa.simpa
              "simpa"
              []
              []
              (Std.Tactic.Simpa.simpaArgsRest
               []
               []
               []
               [(Tactic.simpArgs "[" [(Tactic.simpLemma [] [] `hb')] "]")]
               ["using" (Term.app `same_ray_nonneg_smul_right [`x `ha'])]))])
           []
           (tactic__
            (cdotTk (patternIgnore (token.«· » "·")))
            [(Tactic.intro "intro" [`h])
             []
             (Std.Tactic.obtain
              "obtain"
              [(Std.Tactic.RCases.rcasesPatMed
                [(Std.Tactic.RCases.rcasesPat.tuple
                  "⟨"
                  [(Std.Tactic.RCases.rcasesPatLo
                    (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `r)])
                    [])
                   ","
                   (Std.Tactic.RCases.rcasesPatLo
                    (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `hr)])
                    [])
                   ","
                   (Std.Tactic.RCases.rcasesPatLo
                    (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `rfl)])
                    [])]
                  "⟩")])]
              []
              [":=" [(Term.app `h.exists_nonneg_left [`hx])]])
             []
             (Tactic.simp
              "simp"
              []
              []
              ["only"]
              ["["
               [(Tactic.simpLemma [] [] `inner_smul_right)
                ","
                (Tactic.simpLemma [] [] `real_inner_self_eq_norm_sq)
                ","
                (Tactic.simpLemma [] [] `LinearMap.map_smulₛₗ)
                ","
                (Tactic.simpLemma [] [] `area_form_apply_self)
                ","
                (Tactic.simpLemma [] [] `Algebra.id.smul_eq_mul)
                ","
                (Tactic.simpLemma [] [] `mul_zero)
                ","
                (Tactic.simpLemma [] [] `eq_self_iff_true)
                ","
                (Tactic.simpLemma [] [] `and_true_iff)]
               "]"]
              [])
             []
             (Mathlib.Tactic.Positivity.positivity "positivity")])])))
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
         [(Classical.«tacticBy_cases_:_» "by_cases" [`hx ":"] («term_=_» `x "=" (num "0")))
          []
          (tactic__
           (cdotTk (patternIgnore (token.«· » "·")))
           [(Tactic.simp "simp" [] [] [] ["[" [(Tactic.simpLemma [] [] `hx)] "]"] [])])
          []
          (Tactic.constructor "constructor")
          []
          (tactic__
           (cdotTk (patternIgnore (token.«· » "·")))
           [(Tactic.tacticLet_
             "let"
             (Term.letDecl
              (Term.letIdDecl
               `a
               []
               [(Term.typeSpec ":" (Data.Real.Basic.termℝ "ℝ"))]
               ":="
               (Term.app
                (Term.proj (Term.app `o.basis_right_angle_rotation [`x `hx]) "." `repr)
                [`y (num "0")]))))
            []
            (Tactic.tacticLet_
             "let"
             (Term.letDecl
              (Term.letIdDecl
               `b
               []
               [(Term.typeSpec ":" (Data.Real.Basic.termℝ "ℝ"))]
               ":="
               (Term.app
                (Term.proj (Term.app `o.basis_right_angle_rotation [`x `hx]) "." `repr)
                [`y (num "1")]))))
            []
            (Tactic.tacticSuffices_
             "suffices"
             (Term.sufficesDecl
              []
              (Term.arrow
               («term_∧_»
                («term_≤_»
                 (num "0")
                 "≤"
                 («term_*_»
                  `a
                  "*"
                  («term_^_» (Analysis.Normed.Group.Basic.«term‖_‖» "‖" `x "‖") "^" (num "2"))))
                "∧"
                («term_=_»
                 («term_*_»
                  `b
                  "*"
                  («term_^_» (Analysis.Normed.Group.Basic.«term‖_‖» "‖" `x "‖") "^" (num "2")))
                 "="
                 (num "0")))
               "→"
               (Term.app
                `SameRay
                [(Data.Real.Basic.termℝ "ℝ")
                 `x
                 («term_+_»
                  (Algebra.Group.Defs.«term_•_» `a " • " `x)
                  "+"
                  (Algebra.Group.Defs.«term_•_»
                   `b
                   " • "
                   (Term.app (Orientation.Analysis.InnerProductSpace.TwoDim.termJ "J") [`x])))]))
              (Term.byTactic'
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
                       (Term.proj (Term.app `o.basis_right_angle_rotation [`x `hx]) "." `sum_repr)
                       [`y]))]
                    "]")
                   [])
                  []
                  (Tactic.simp
                   "simp"
                   []
                   []
                   ["only"]
                   ["["
                    [(Tactic.simpLemma [] [] `Fin.sum_univ_succ)
                     ","
                     (Tactic.simpLemma [] [] `coe_basis_right_angle_rotation)]
                    "]"]
                   [])
                  []
                  (Tactic.dsimp "dsimp" [] [] [] [] [])
                  []
                  (Tactic.simp
                   "simp"
                   []
                   []
                   ["only"]
                   ["["
                    [(Tactic.simpLemma [] [] `o.area_form_apply_self)
                     ","
                     (Tactic.simpLemma [] [] `map_smul)
                     ","
                     (Tactic.simpLemma [] [] `map_add)
                     ","
                     (Tactic.simpLemma [] [] `map_zero)
                     ","
                     (Tactic.simpLemma [] [] `inner_smul_left)
                     ","
                     (Tactic.simpLemma [] [] `inner_smul_right)
                     ","
                     (Tactic.simpLemma [] [] `inner_add_left)
                     ","
                     (Tactic.simpLemma [] [] `inner_add_right)
                     ","
                     (Tactic.simpLemma [] [] `inner_zero_right)
                     ","
                     (Tactic.simpLemma [] [] `LinearMap.add_apply)
                     ","
                     (Tactic.simpLemma [] [] `Matrix.cons_val_one)]
                    "]"]
                   [])
                  []
                  (Tactic.dsimp "dsimp" [] [] [] [] [])
                  []
                  (Tactic.simp
                   "simp"
                   []
                   []
                   ["only"]
                   ["["
                    [(Tactic.simpLemma [] [] `o.area_form_right_angle_rotation_right)
                     ","
                     (Tactic.simpLemma [] [] `mul_zero)
                     ","
                     (Tactic.simpLemma [] [] `add_zero)
                     ","
                     (Tactic.simpLemma [] [] `zero_add)
                     ","
                     (Tactic.simpLemma [] [] `neg_zero)
                     ","
                     (Tactic.simpLemma [] [] `o.inner_right_angle_rotation_right)
                     ","
                     (Tactic.simpLemma [] [] `o.area_form_apply_self)
                     ","
                     (Tactic.simpLemma [] [] `real_inner_self_eq_norm_sq)]
                    "]"]
                   [])
                  []
                  (Tactic.exact "exact" `this)])))))
            []
            (Std.Tactic.rintro
             "rintro"
             [(Std.Tactic.RCases.rintroPat.one
               (Std.Tactic.RCases.rcasesPat.tuple
                "⟨"
                [(Std.Tactic.RCases.rcasesPatLo
                  (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `ha)])
                  [])
                 ","
                 (Std.Tactic.RCases.rcasesPatLo
                  (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `hb)])
                  [])]
                "⟩"))]
             [])
            []
            (Tactic.tacticHave_
             "have"
             (Term.haveDecl
              (Term.haveIdDecl
               [`hx' []]
               [(Term.typeSpec
                 ":"
                 («term_<_» (num "0") "<" (Analysis.Normed.Group.Basic.«term‖_‖» "‖" `x "‖")))]
               ":="
               (Term.byTactic
                "by"
                (Tactic.tacticSeq
                 (Tactic.tacticSeq1Indented
                  [(Std.Tactic.Simpa.simpa
                    "simpa"
                    []
                    []
                    (Std.Tactic.Simpa.simpaArgsRest [] [] [] [] ["using" `hx]))]))))))
            []
            (Tactic.tacticHave_
             "have"
             (Term.haveDecl
              (Term.haveIdDecl
               [`ha' []]
               [(Term.typeSpec ":" («term_≤_» (num "0") "≤" `a))]
               ":="
               (Term.app
                `nonneg_of_mul_nonneg_left
                [`ha
                 (Term.byTactic
                  "by"
                  (Tactic.tacticSeq
                   (Tactic.tacticSeq1Indented
                    [(Mathlib.Tactic.Positivity.positivity "positivity")])))]))))
            []
            (Tactic.tacticHave_
             "have"
             (Term.haveDecl
              (Term.haveIdDecl
               [`hb' []]
               [(Term.typeSpec ":" («term_=_» `b "=" (num "0")))]
               ":="
               (Term.app
                `eq_zero_of_ne_zero_of_mul_right_eq_zero
                [(Term.app `pow_ne_zero [(num "2") `hx'.ne']) `hb]))))
            []
            (Std.Tactic.Simpa.simpa
             "simpa"
             []
             []
             (Std.Tactic.Simpa.simpaArgsRest
              []
              []
              []
              [(Tactic.simpArgs "[" [(Tactic.simpLemma [] [] `hb')] "]")]
              ["using" (Term.app `same_ray_nonneg_smul_right [`x `ha'])]))])
          []
          (tactic__
           (cdotTk (patternIgnore (token.«· » "·")))
           [(Tactic.intro "intro" [`h])
            []
            (Std.Tactic.obtain
             "obtain"
             [(Std.Tactic.RCases.rcasesPatMed
               [(Std.Tactic.RCases.rcasesPat.tuple
                 "⟨"
                 [(Std.Tactic.RCases.rcasesPatLo
                   (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `r)])
                   [])
                  ","
                  (Std.Tactic.RCases.rcasesPatLo
                   (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `hr)])
                   [])
                  ","
                  (Std.Tactic.RCases.rcasesPatLo
                   (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `rfl)])
                   [])]
                 "⟩")])]
             []
             [":=" [(Term.app `h.exists_nonneg_left [`hx])]])
            []
            (Tactic.simp
             "simp"
             []
             []
             ["only"]
             ["["
              [(Tactic.simpLemma [] [] `inner_smul_right)
               ","
               (Tactic.simpLemma [] [] `real_inner_self_eq_norm_sq)
               ","
               (Tactic.simpLemma [] [] `LinearMap.map_smulₛₗ)
               ","
               (Tactic.simpLemma [] [] `area_form_apply_self)
               ","
               (Tactic.simpLemma [] [] `Algebra.id.smul_eq_mul)
               ","
               (Tactic.simpLemma [] [] `mul_zero)
               ","
               (Tactic.simpLemma [] [] `eq_self_iff_true)
               ","
               (Tactic.simpLemma [] [] `and_true_iff)]
              "]"]
             [])
            []
            (Mathlib.Tactic.Positivity.positivity "positivity")])])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (tactic__
       (cdotTk (patternIgnore (token.«· » "·")))
       [(Tactic.intro "intro" [`h])
        []
        (Std.Tactic.obtain
         "obtain"
         [(Std.Tactic.RCases.rcasesPatMed
           [(Std.Tactic.RCases.rcasesPat.tuple
             "⟨"
             [(Std.Tactic.RCases.rcasesPatLo
               (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `r)])
               [])
              ","
              (Std.Tactic.RCases.rcasesPatLo
               (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `hr)])
               [])
              ","
              (Std.Tactic.RCases.rcasesPatLo
               (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `rfl)])
               [])]
             "⟩")])]
         []
         [":=" [(Term.app `h.exists_nonneg_left [`hx])]])
        []
        (Tactic.simp
         "simp"
         []
         []
         ["only"]
         ["["
          [(Tactic.simpLemma [] [] `inner_smul_right)
           ","
           (Tactic.simpLemma [] [] `real_inner_self_eq_norm_sq)
           ","
           (Tactic.simpLemma [] [] `LinearMap.map_smulₛₗ)
           ","
           (Tactic.simpLemma [] [] `area_form_apply_self)
           ","
           (Tactic.simpLemma [] [] `Algebra.id.smul_eq_mul)
           ","
           (Tactic.simpLemma [] [] `mul_zero)
           ","
           (Tactic.simpLemma [] [] `eq_self_iff_true)
           ","
           (Tactic.simpLemma [] [] `and_true_iff)]
          "]"]
         [])
        []
        (Mathlib.Tactic.Positivity.positivity "positivity")])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Mathlib.Tactic.Positivity.positivity "positivity")
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.simp
       "simp"
       []
       []
       ["only"]
       ["["
        [(Tactic.simpLemma [] [] `inner_smul_right)
         ","
         (Tactic.simpLemma [] [] `real_inner_self_eq_norm_sq)
         ","
         (Tactic.simpLemma [] [] `LinearMap.map_smulₛₗ)
         ","
         (Tactic.simpLemma [] [] `area_form_apply_self)
         ","
         (Tactic.simpLemma [] [] `Algebra.id.smul_eq_mul)
         ","
         (Tactic.simpLemma [] [] `mul_zero)
         ","
         (Tactic.simpLemma [] [] `eq_self_iff_true)
         ","
         (Tactic.simpLemma [] [] `and_true_iff)]
        "]"]
       [])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `and_true_iff
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `eq_self_iff_true
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `mul_zero
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `Algebra.id.smul_eq_mul
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `area_form_apply_self
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `LinearMap.map_smulₛₗ
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `real_inner_self_eq_norm_sq
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `inner_smul_right
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Std.Tactic.obtain
       "obtain"
       [(Std.Tactic.RCases.rcasesPatMed
         [(Std.Tactic.RCases.rcasesPat.tuple
           "⟨"
           [(Std.Tactic.RCases.rcasesPatLo
             (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `r)])
             [])
            ","
            (Std.Tactic.RCases.rcasesPatLo
             (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `hr)])
             [])
            ","
            (Std.Tactic.RCases.rcasesPatLo
             (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `rfl)])
             [])]
           "⟩")])]
       []
       [":=" [(Term.app `h.exists_nonneg_left [`hx])]])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `h.exists_nonneg_left [`hx])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `hx
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `h.exists_nonneg_left
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.intro "intro" [`h])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `h
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (tactic__
       (cdotTk (patternIgnore (token.«· » "·")))
       [(Tactic.tacticLet_
         "let"
         (Term.letDecl
          (Term.letIdDecl
           `a
           []
           [(Term.typeSpec ":" (Data.Real.Basic.termℝ "ℝ"))]
           ":="
           (Term.app
            (Term.proj (Term.app `o.basis_right_angle_rotation [`x `hx]) "." `repr)
            [`y (num "0")]))))
        []
        (Tactic.tacticLet_
         "let"
         (Term.letDecl
          (Term.letIdDecl
           `b
           []
           [(Term.typeSpec ":" (Data.Real.Basic.termℝ "ℝ"))]
           ":="
           (Term.app
            (Term.proj (Term.app `o.basis_right_angle_rotation [`x `hx]) "." `repr)
            [`y (num "1")]))))
        []
        (Tactic.tacticSuffices_
         "suffices"
         (Term.sufficesDecl
          []
          (Term.arrow
           («term_∧_»
            («term_≤_»
             (num "0")
             "≤"
             («term_*_»
              `a
              "*"
              («term_^_» (Analysis.Normed.Group.Basic.«term‖_‖» "‖" `x "‖") "^" (num "2"))))
            "∧"
            («term_=_»
             («term_*_»
              `b
              "*"
              («term_^_» (Analysis.Normed.Group.Basic.«term‖_‖» "‖" `x "‖") "^" (num "2")))
             "="
             (num "0")))
           "→"
           (Term.app
            `SameRay
            [(Data.Real.Basic.termℝ "ℝ")
             `x
             («term_+_»
              (Algebra.Group.Defs.«term_•_» `a " • " `x)
              "+"
              (Algebra.Group.Defs.«term_•_»
               `b
               " • "
               (Term.app (Orientation.Analysis.InnerProductSpace.TwoDim.termJ "J") [`x])))]))
          (Term.byTactic'
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
                   (Term.proj (Term.app `o.basis_right_angle_rotation [`x `hx]) "." `sum_repr)
                   [`y]))]
                "]")
               [])
              []
              (Tactic.simp
               "simp"
               []
               []
               ["only"]
               ["["
                [(Tactic.simpLemma [] [] `Fin.sum_univ_succ)
                 ","
                 (Tactic.simpLemma [] [] `coe_basis_right_angle_rotation)]
                "]"]
               [])
              []
              (Tactic.dsimp "dsimp" [] [] [] [] [])
              []
              (Tactic.simp
               "simp"
               []
               []
               ["only"]
               ["["
                [(Tactic.simpLemma [] [] `o.area_form_apply_self)
                 ","
                 (Tactic.simpLemma [] [] `map_smul)
                 ","
                 (Tactic.simpLemma [] [] `map_add)
                 ","
                 (Tactic.simpLemma [] [] `map_zero)
                 ","
                 (Tactic.simpLemma [] [] `inner_smul_left)
                 ","
                 (Tactic.simpLemma [] [] `inner_smul_right)
                 ","
                 (Tactic.simpLemma [] [] `inner_add_left)
                 ","
                 (Tactic.simpLemma [] [] `inner_add_right)
                 ","
                 (Tactic.simpLemma [] [] `inner_zero_right)
                 ","
                 (Tactic.simpLemma [] [] `LinearMap.add_apply)
                 ","
                 (Tactic.simpLemma [] [] `Matrix.cons_val_one)]
                "]"]
               [])
              []
              (Tactic.dsimp "dsimp" [] [] [] [] [])
              []
              (Tactic.simp
               "simp"
               []
               []
               ["only"]
               ["["
                [(Tactic.simpLemma [] [] `o.area_form_right_angle_rotation_right)
                 ","
                 (Tactic.simpLemma [] [] `mul_zero)
                 ","
                 (Tactic.simpLemma [] [] `add_zero)
                 ","
                 (Tactic.simpLemma [] [] `zero_add)
                 ","
                 (Tactic.simpLemma [] [] `neg_zero)
                 ","
                 (Tactic.simpLemma [] [] `o.inner_right_angle_rotation_right)
                 ","
                 (Tactic.simpLemma [] [] `o.area_form_apply_self)
                 ","
                 (Tactic.simpLemma [] [] `real_inner_self_eq_norm_sq)]
                "]"]
               [])
              []
              (Tactic.exact "exact" `this)])))))
        []
        (Std.Tactic.rintro
         "rintro"
         [(Std.Tactic.RCases.rintroPat.one
           (Std.Tactic.RCases.rcasesPat.tuple
            "⟨"
            [(Std.Tactic.RCases.rcasesPatLo
              (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `ha)])
              [])
             ","
             (Std.Tactic.RCases.rcasesPatLo
              (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `hb)])
              [])]
            "⟩"))]
         [])
        []
        (Tactic.tacticHave_
         "have"
         (Term.haveDecl
          (Term.haveIdDecl
           [`hx' []]
           [(Term.typeSpec
             ":"
             («term_<_» (num "0") "<" (Analysis.Normed.Group.Basic.«term‖_‖» "‖" `x "‖")))]
           ":="
           (Term.byTactic
            "by"
            (Tactic.tacticSeq
             (Tactic.tacticSeq1Indented
              [(Std.Tactic.Simpa.simpa
                "simpa"
                []
                []
                (Std.Tactic.Simpa.simpaArgsRest [] [] [] [] ["using" `hx]))]))))))
        []
        (Tactic.tacticHave_
         "have"
         (Term.haveDecl
          (Term.haveIdDecl
           [`ha' []]
           [(Term.typeSpec ":" («term_≤_» (num "0") "≤" `a))]
           ":="
           (Term.app
            `nonneg_of_mul_nonneg_left
            [`ha
             (Term.byTactic
              "by"
              (Tactic.tacticSeq
               (Tactic.tacticSeq1Indented
                [(Mathlib.Tactic.Positivity.positivity "positivity")])))]))))
        []
        (Tactic.tacticHave_
         "have"
         (Term.haveDecl
          (Term.haveIdDecl
           [`hb' []]
           [(Term.typeSpec ":" («term_=_» `b "=" (num "0")))]
           ":="
           (Term.app
            `eq_zero_of_ne_zero_of_mul_right_eq_zero
            [(Term.app `pow_ne_zero [(num "2") `hx'.ne']) `hb]))))
        []
        (Std.Tactic.Simpa.simpa
         "simpa"
         []
         []
         (Std.Tactic.Simpa.simpaArgsRest
          []
          []
          []
          [(Tactic.simpArgs "[" [(Tactic.simpLemma [] [] `hb')] "]")]
          ["using" (Term.app `same_ray_nonneg_smul_right [`x `ha'])]))])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Std.Tactic.Simpa.simpa
       "simpa"
       []
       []
       (Std.Tactic.Simpa.simpaArgsRest
        []
        []
        []
        [(Tactic.simpArgs "[" [(Tactic.simpLemma [] [] `hb')] "]")]
        ["using" (Term.app `same_ray_nonneg_smul_right [`x `ha'])]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `same_ray_nonneg_smul_right [`x `ha'])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `ha'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `x
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `same_ray_nonneg_smul_right
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `hb'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.tacticHave_
       "have"
       (Term.haveDecl
        (Term.haveIdDecl
         [`hb' []]
         [(Term.typeSpec ":" («term_=_» `b "=" (num "0")))]
         ":="
         (Term.app
          `eq_zero_of_ne_zero_of_mul_right_eq_zero
          [(Term.app `pow_ne_zero [(num "2") `hx'.ne']) `hb]))))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       `eq_zero_of_ne_zero_of_mul_right_eq_zero
       [(Term.app `pow_ne_zero [(num "2") `hx'.ne']) `hb])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `hb
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.app `pow_ne_zero [(num "2") `hx'.ne'])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `hx'.ne'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'num', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'num', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (num "2")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `pow_ne_zero
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023,
     term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.app `pow_ne_zero [(num "2") `hx'.ne'])
     ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `eq_zero_of_ne_zero_of_mul_right_eq_zero
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_=_» `b "=" (num "0"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (num "0")
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 50, term))
      `b
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1024, (none, [anonymous]) <=? (some 50, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 50, (some 51, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.tacticHave_
       "have"
       (Term.haveDecl
        (Term.haveIdDecl
         [`ha' []]
         [(Term.typeSpec ":" («term_≤_» (num "0") "≤" `a))]
         ":="
         (Term.app
          `nonneg_of_mul_nonneg_left
          [`ha
           (Term.byTactic
            "by"
            (Tactic.tacticSeq
             (Tactic.tacticSeq1Indented
              [(Mathlib.Tactic.Positivity.positivity "positivity")])))]))))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       `nonneg_of_mul_nonneg_left
       [`ha
        (Term.byTactic
         "by"
         (Tactic.tacticSeq
          (Tactic.tacticSeq1Indented [(Mathlib.Tactic.Positivity.positivity "positivity")])))])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.byTactic', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.byTactic', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.byTactic
       "by"
       (Tactic.tacticSeq
        (Tactic.tacticSeq1Indented [(Mathlib.Tactic.Positivity.positivity "positivity")])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Mathlib.Tactic.Positivity.positivity "positivity")
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 0,
     tactic) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.byTactic
      "by"
      (Tactic.tacticSeq
       (Tactic.tacticSeq1Indented [(Mathlib.Tactic.Positivity.positivity "positivity")])))
     ")")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `ha
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `nonneg_of_mul_nonneg_left
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_≤_» (num "0") "≤" `a)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `a
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 50, term))
      (num "0")
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1024, (none, [anonymous]) <=? (some 50, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 50, (some 51, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.tacticHave_
       "have"
       (Term.haveDecl
        (Term.haveIdDecl
         [`hx' []]
         [(Term.typeSpec
           ":"
           («term_<_» (num "0") "<" (Analysis.Normed.Group.Basic.«term‖_‖» "‖" `x "‖")))]
         ":="
         (Term.byTactic
          "by"
          (Tactic.tacticSeq
           (Tactic.tacticSeq1Indented
            [(Std.Tactic.Simpa.simpa
              "simpa"
              []
              []
              (Std.Tactic.Simpa.simpaArgsRest [] [] [] [] ["using" `hx]))]))))))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.byTactic
       "by"
       (Tactic.tacticSeq
        (Tactic.tacticSeq1Indented
         [(Std.Tactic.Simpa.simpa
           "simpa"
           []
           []
           (Std.Tactic.Simpa.simpaArgsRest [] [] [] [] ["using" `hx]))])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Std.Tactic.Simpa.simpa
       "simpa"
       []
       []
       (Std.Tactic.Simpa.simpaArgsRest [] [] [] [] ["using" `hx]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `hx
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, tactic) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_<_» (num "0") "<" (Analysis.Normed.Group.Basic.«term‖_‖» "‖" `x "‖"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Analysis.Normed.Group.Basic.«term‖_‖» "‖" `x "‖")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `x
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 50, term))
      (num "0")
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1024, (none, [anonymous]) <=? (some 50, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 50, (some 51, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Std.Tactic.rintro
       "rintro"
       [(Std.Tactic.RCases.rintroPat.one
         (Std.Tactic.RCases.rcasesPat.tuple
          "⟨"
          [(Std.Tactic.RCases.rcasesPatLo
            (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `ha)])
            [])
           ","
           (Std.Tactic.RCases.rcasesPatLo
            (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `hb)])
            [])]
          "⟩"))]
       [])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.tacticSuffices_
       "suffices"
       (Term.sufficesDecl
        []
        (Term.arrow
         («term_∧_»
          («term_≤_»
           (num "0")
           "≤"
           («term_*_»
            `a
            "*"
            («term_^_» (Analysis.Normed.Group.Basic.«term‖_‖» "‖" `x "‖") "^" (num "2"))))
          "∧"
          («term_=_»
           («term_*_»
            `b
            "*"
            («term_^_» (Analysis.Normed.Group.Basic.«term‖_‖» "‖" `x "‖") "^" (num "2")))
           "="
           (num "0")))
         "→"
         (Term.app
          `SameRay
          [(Data.Real.Basic.termℝ "ℝ")
           `x
           («term_+_»
            (Algebra.Group.Defs.«term_•_» `a " • " `x)
            "+"
            (Algebra.Group.Defs.«term_•_»
             `b
             " • "
             (Term.app (Orientation.Analysis.InnerProductSpace.TwoDim.termJ "J") [`x])))]))
        (Term.byTactic'
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
                 (Term.proj (Term.app `o.basis_right_angle_rotation [`x `hx]) "." `sum_repr)
                 [`y]))]
              "]")
             [])
            []
            (Tactic.simp
             "simp"
             []
             []
             ["only"]
             ["["
              [(Tactic.simpLemma [] [] `Fin.sum_univ_succ)
               ","
               (Tactic.simpLemma [] [] `coe_basis_right_angle_rotation)]
              "]"]
             [])
            []
            (Tactic.dsimp "dsimp" [] [] [] [] [])
            []
            (Tactic.simp
             "simp"
             []
             []
             ["only"]
             ["["
              [(Tactic.simpLemma [] [] `o.area_form_apply_self)
               ","
               (Tactic.simpLemma [] [] `map_smul)
               ","
               (Tactic.simpLemma [] [] `map_add)
               ","
               (Tactic.simpLemma [] [] `map_zero)
               ","
               (Tactic.simpLemma [] [] `inner_smul_left)
               ","
               (Tactic.simpLemma [] [] `inner_smul_right)
               ","
               (Tactic.simpLemma [] [] `inner_add_left)
               ","
               (Tactic.simpLemma [] [] `inner_add_right)
               ","
               (Tactic.simpLemma [] [] `inner_zero_right)
               ","
               (Tactic.simpLemma [] [] `LinearMap.add_apply)
               ","
               (Tactic.simpLemma [] [] `Matrix.cons_val_one)]
              "]"]
             [])
            []
            (Tactic.dsimp "dsimp" [] [] [] [] [])
            []
            (Tactic.simp
             "simp"
             []
             []
             ["only"]
             ["["
              [(Tactic.simpLemma [] [] `o.area_form_right_angle_rotation_right)
               ","
               (Tactic.simpLemma [] [] `mul_zero)
               ","
               (Tactic.simpLemma [] [] `add_zero)
               ","
               (Tactic.simpLemma [] [] `zero_add)
               ","
               (Tactic.simpLemma [] [] `neg_zero)
               ","
               (Tactic.simpLemma [] [] `o.inner_right_angle_rotation_right)
               ","
               (Tactic.simpLemma [] [] `o.area_form_apply_self)
               ","
               (Tactic.simpLemma [] [] `real_inner_self_eq_norm_sq)]
              "]"]
             [])
            []
            (Tactic.exact "exact" `this)])))))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.byTactic'', expected 'Lean.Parser.Term.fromTerm'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.exact "exact" `this)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `this
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
        [(Tactic.simpLemma [] [] `o.area_form_right_angle_rotation_right)
         ","
         (Tactic.simpLemma [] [] `mul_zero)
         ","
         (Tactic.simpLemma [] [] `add_zero)
         ","
         (Tactic.simpLemma [] [] `zero_add)
         ","
         (Tactic.simpLemma [] [] `neg_zero)
         ","
         (Tactic.simpLemma [] [] `o.inner_right_angle_rotation_right)
         ","
         (Tactic.simpLemma [] [] `o.area_form_apply_self)
         ","
         (Tactic.simpLemma [] [] `real_inner_self_eq_norm_sq)]
        "]"]
       [])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `real_inner_self_eq_norm_sq
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `o.area_form_apply_self
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `o.inner_right_angle_rotation_right
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `neg_zero
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `zero_add
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `add_zero
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `mul_zero
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `o.area_form_right_angle_rotation_right
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.dsimp "dsimp" [] [] [] [] [])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.simp
       "simp"
       []
       []
       ["only"]
       ["["
        [(Tactic.simpLemma [] [] `o.area_form_apply_self)
         ","
         (Tactic.simpLemma [] [] `map_smul)
         ","
         (Tactic.simpLemma [] [] `map_add)
         ","
         (Tactic.simpLemma [] [] `map_zero)
         ","
         (Tactic.simpLemma [] [] `inner_smul_left)
         ","
         (Tactic.simpLemma [] [] `inner_smul_right)
         ","
         (Tactic.simpLemma [] [] `inner_add_left)
         ","
         (Tactic.simpLemma [] [] `inner_add_right)
         ","
         (Tactic.simpLemma [] [] `inner_zero_right)
         ","
         (Tactic.simpLemma [] [] `LinearMap.add_apply)
         ","
         (Tactic.simpLemma [] [] `Matrix.cons_val_one)]
        "]"]
       [])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `Matrix.cons_val_one
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `LinearMap.add_apply
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `inner_zero_right
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `inner_add_right
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `inner_add_left
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `inner_smul_right
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `inner_smul_left
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `map_zero
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `map_add
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
      `o.area_form_apply_self
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.dsimp "dsimp" [] [] [] [] [])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.simp
       "simp"
       []
       []
       ["only"]
       ["["
        [(Tactic.simpLemma [] [] `Fin.sum_univ_succ)
         ","
         (Tactic.simpLemma [] [] `coe_basis_right_angle_rotation)]
        "]"]
       [])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `coe_basis_right_angle_rotation
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `Fin.sum_univ_succ
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
          (Term.app
           (Term.proj (Term.app `o.basis_right_angle_rotation [`x `hx]) "." `sum_repr)
           [`y]))]
        "]")
       [])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app (Term.proj (Term.app `o.basis_right_angle_rotation [`x `hx]) "." `sum_repr) [`y])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `y
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (Term.proj (Term.app `o.basis_right_angle_rotation [`x `hx]) "." `sum_repr)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.app `o.basis_right_angle_rotation [`x `hx])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `hx
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `x
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `o.basis_right_angle_rotation
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.app `o.basis_right_angle_rotation [`x `hx])
     ")")
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
      (Term.arrow
       («term_∧_»
        («term_≤_»
         (num "0")
         "≤"
         («term_*_»
          `a
          "*"
          («term_^_» (Analysis.Normed.Group.Basic.«term‖_‖» "‖" `x "‖") "^" (num "2"))))
        "∧"
        («term_=_»
         («term_*_»
          `b
          "*"
          («term_^_» (Analysis.Normed.Group.Basic.«term‖_‖» "‖" `x "‖") "^" (num "2")))
         "="
         (num "0")))
       "→"
       (Term.app
        `SameRay
        [(Data.Real.Basic.termℝ "ℝ")
         `x
         («term_+_»
          (Algebra.Group.Defs.«term_•_» `a " • " `x)
          "+"
          (Algebra.Group.Defs.«term_•_»
           `b
           " • "
           (Term.app (Orientation.Analysis.InnerProductSpace.TwoDim.termJ "J") [`x])))]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       `SameRay
       [(Data.Real.Basic.termℝ "ℝ")
        `x
        («term_+_»
         (Algebra.Group.Defs.«term_•_» `a " • " `x)
         "+"
         (Algebra.Group.Defs.«term_•_»
          `b
          " • "
          (Term.app (Orientation.Analysis.InnerProductSpace.TwoDim.termJ "J") [`x])))])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_+_»', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_+_»', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_+_»
       (Algebra.Group.Defs.«term_•_» `a " • " `x)
       "+"
       (Algebra.Group.Defs.«term_•_»
        `b
        " • "
        (Term.app (Orientation.Analysis.InnerProductSpace.TwoDim.termJ "J") [`x])))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Algebra.Group.Defs.«term_•_»
       `b
       " • "
       (Term.app (Orientation.Analysis.InnerProductSpace.TwoDim.termJ "J") [`x]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app (Orientation.Analysis.InnerProductSpace.TwoDim.termJ "J") [`x])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `x
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (Orientation.Analysis.InnerProductSpace.TwoDim.termJ "J")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Orientation.Analysis.InnerProductSpace.TwoDim.termJ', expected 'Orientation.Analysis.InnerProductSpace.TwoDim.termJ._@.Analysis.InnerProductSpace.TwoDim._hyg.50'
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
  nonneg_inner_and_area_form_eq_zero_iff_same_ray
  ( x y : E ) : 0 ≤ ⟪ x , y ⟫ ∧ ω x y = 0 ↔ SameRay ℝ x y
  :=
    by
      by_cases hx : x = 0
        · simp [ hx ]
        constructor
        ·
          let a : ℝ := o.basis_right_angle_rotation x hx . repr y 0
            let b : ℝ := o.basis_right_angle_rotation x hx . repr y 1
            suffices
              0 ≤ a * ‖ x ‖ ^ 2 ∧ b * ‖ x ‖ ^ 2 = 0 → SameRay ℝ x a • x + b • J x
                by
                  rw [ ← o.basis_right_angle_rotation x hx . sum_repr y ]
                    simp only [ Fin.sum_univ_succ , coe_basis_right_angle_rotation ]
                    dsimp
                    simp
                      only
                      [
                        o.area_form_apply_self
                          ,
                          map_smul
                          ,
                          map_add
                          ,
                          map_zero
                          ,
                          inner_smul_left
                          ,
                          inner_smul_right
                          ,
                          inner_add_left
                          ,
                          inner_add_right
                          ,
                          inner_zero_right
                          ,
                          LinearMap.add_apply
                          ,
                          Matrix.cons_val_one
                        ]
                    dsimp
                    simp
                      only
                      [
                        o.area_form_right_angle_rotation_right
                          ,
                          mul_zero
                          ,
                          add_zero
                          ,
                          zero_add
                          ,
                          neg_zero
                          ,
                          o.inner_right_angle_rotation_right
                          ,
                          o.area_form_apply_self
                          ,
                          real_inner_self_eq_norm_sq
                        ]
                    exact this
            rintro ⟨ ha , hb ⟩
            have hx' : 0 < ‖ x ‖ := by simpa using hx
            have ha' : 0 ≤ a := nonneg_of_mul_nonneg_left ha by positivity
            have hb' : b = 0 := eq_zero_of_ne_zero_of_mul_right_eq_zero pow_ne_zero 2 hx'.ne' hb
            simpa [ hb' ] using same_ray_nonneg_smul_right x ha'
        ·
          intro h
            obtain ⟨ r , hr , rfl ⟩ := h.exists_nonneg_left hx
            simp
              only
              [
                inner_smul_right
                  ,
                  real_inner_self_eq_norm_sq
                  ,
                  LinearMap.map_smulₛₗ
                  ,
                  area_form_apply_self
                  ,
                  Algebra.id.smul_eq_mul
                  ,
                  mul_zero
                  ,
                  eq_self_iff_true
                  ,
                  and_true_iff
                ]
            positivity
#align
  orientation.nonneg_inner_and_area_form_eq_zero_iff_same_ray Orientation.nonneg_inner_and_area_form_eq_zero_iff_same_ray

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers
      [(Command.docComment
        "/--"
        "A complex-valued real-bilinear map on an oriented real inner product space of dimension 2. Its\nreal part is the inner product and its imaginary part is `orientation.area_form`.\n\nOn `ℂ` with the standard orientation, `kahler w z = conj w * z`; see `complex.kahler`. -/")]
      []
      []
      []
      []
      [])
     (Command.def
      "def"
      (Command.declId `kahler [])
      (Command.optDeclSig
       []
       [(Term.typeSpec
         ":"
         (Algebra.Module.LinearMap.«term_→ₗ[_]_»
          `E
          " →ₗ["
          (Data.Real.Basic.termℝ "ℝ")
          "] "
          (Algebra.Module.LinearMap.«term_→ₗ[_]_»
           `E
           " →ₗ["
           (Data.Real.Basic.termℝ "ℝ")
           "] "
           (Data.Complex.Basic.termℂ "ℂ"))))])
      (Command.declValSimple
       ":="
       («term_+_»
        (LinearMap.Algebra.Module.LinearMap.«term_∘ₗ_»
         (Term.app
          `LinearMap.llcomp
          [(Data.Real.Basic.termℝ "ℝ")
           `E
           (Data.Real.Basic.termℝ "ℝ")
           (Data.Complex.Basic.termℂ "ℂ")
           `Complex.ofRealClm])
         " ∘ₗ "
         (Term.app
          (Term.explicit "@" `innerₛₗ)
          [(Data.Real.Basic.termℝ "ℝ") `E (Term.hole "_") (Term.hole "_")]))
        "+"
        (LinearMap.Algebra.Module.LinearMap.«term_∘ₗ_»
         (Term.app
          `LinearMap.llcomp
          [(Data.Real.Basic.termℝ "ℝ")
           `E
           (Data.Real.Basic.termℝ "ℝ")
           (Data.Complex.Basic.termℂ "ℂ")
           (Term.app
            (Term.proj
             (Term.app
              `LinearMap.lsmul
              [(Data.Real.Basic.termℝ "ℝ") (Data.Complex.Basic.termℂ "ℂ")])
             "."
             `flip)
            [`Complex.i])])
         " ∘ₗ "
         (Orientation.Analysis.InnerProductSpace.TwoDim.termω "ω")))
       [])
      []
      []
      []))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.abbrev'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_+_»
       (LinearMap.Algebra.Module.LinearMap.«term_∘ₗ_»
        (Term.app
         `LinearMap.llcomp
         [(Data.Real.Basic.termℝ "ℝ")
          `E
          (Data.Real.Basic.termℝ "ℝ")
          (Data.Complex.Basic.termℂ "ℂ")
          `Complex.ofRealClm])
        " ∘ₗ "
        (Term.app
         (Term.explicit "@" `innerₛₗ)
         [(Data.Real.Basic.termℝ "ℝ") `E (Term.hole "_") (Term.hole "_")]))
       "+"
       (LinearMap.Algebra.Module.LinearMap.«term_∘ₗ_»
        (Term.app
         `LinearMap.llcomp
         [(Data.Real.Basic.termℝ "ℝ")
          `E
          (Data.Real.Basic.termℝ "ℝ")
          (Data.Complex.Basic.termℂ "ℂ")
          (Term.app
           (Term.proj
            (Term.app `LinearMap.lsmul [(Data.Real.Basic.termℝ "ℝ") (Data.Complex.Basic.termℂ "ℂ")])
            "."
            `flip)
           [`Complex.i])])
        " ∘ₗ "
        (Orientation.Analysis.InnerProductSpace.TwoDim.termω "ω")))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (LinearMap.Algebra.Module.LinearMap.«term_∘ₗ_»
       (Term.app
        `LinearMap.llcomp
        [(Data.Real.Basic.termℝ "ℝ")
         `E
         (Data.Real.Basic.termℝ "ℝ")
         (Data.Complex.Basic.termℂ "ℂ")
         (Term.app
          (Term.proj
           (Term.app `LinearMap.lsmul [(Data.Real.Basic.termℝ "ℝ") (Data.Complex.Basic.termℂ "ℂ")])
           "."
           `flip)
          [`Complex.i])])
       " ∘ₗ "
       (Orientation.Analysis.InnerProductSpace.TwoDim.termω "ω"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Orientation.Analysis.InnerProductSpace.TwoDim.termω "ω")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Orientation.Analysis.InnerProductSpace.TwoDim.termω', expected 'Orientation.Analysis.InnerProductSpace.TwoDim.termω._@.Analysis.InnerProductSpace.TwoDim._hyg.7'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.declValSimple', expected 'Lean.Parser.Command.declValEqns'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.declValSimple', expected 'Lean.Parser.Command.whereStructInst'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.theorem'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.opaque'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.instance'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.axiom'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.example'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.inductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.classInductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.structure'-/-- failed to format: format: uncaught backtrack exception
/--
    A complex-valued real-bilinear map on an oriented real inner product space of dimension 2. Its
    real part is the inner product and its imaginary part is `orientation.area_form`.
    
    On `ℂ` with the standard orientation, `kahler w z = conj w * z`; see `complex.kahler`. -/
  def
    kahler
    : E →ₗ[ ℝ ] E →ₗ[ ℝ ] ℂ
    :=
      LinearMap.llcomp ℝ E ℝ ℂ Complex.ofRealClm ∘ₗ @ innerₛₗ ℝ E _ _
        +
        LinearMap.llcomp ℝ E ℝ ℂ LinearMap.lsmul ℝ ℂ . flip Complex.i ∘ₗ ω
#align orientation.kahler Orientation.kahler

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers [] [] [] [] [] [])
     (Command.theorem
      "theorem"
      (Command.declId `kahler_apply_apply [])
      (Command.declSig
       [(Term.explicitBinder "(" [`x `y] [":" `E] [] ")")]
       (Term.typeSpec
        ":"
        («term_=_»
         (Term.app (Term.proj `o "." `kahler) [`x `y])
         "="
         («term_+_»
          (RealInnerProductSpace.Analysis.InnerProductSpace.Basic.inner.real "⟪" `x ", " `y "⟫")
          "+"
          (Algebra.Group.Defs.«term_•_»
           (Term.app (Orientation.Analysis.InnerProductSpace.TwoDim.termω "ω") [`x `y])
           " • "
           `Complex.i)))))
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
       (Term.app (Term.proj `o "." `kahler) [`x `y])
       "="
       («term_+_»
        (RealInnerProductSpace.Analysis.InnerProductSpace.Basic.inner.real "⟪" `x ", " `y "⟫")
        "+"
        (Algebra.Group.Defs.«term_•_»
         (Term.app (Orientation.Analysis.InnerProductSpace.TwoDim.termω "ω") [`x `y])
         " • "
         `Complex.i)))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_+_»
       (RealInnerProductSpace.Analysis.InnerProductSpace.Basic.inner.real "⟪" `x ", " `y "⟫")
       "+"
       (Algebra.Group.Defs.«term_•_»
        (Term.app (Orientation.Analysis.InnerProductSpace.TwoDim.termω "ω") [`x `y])
        " • "
        `Complex.i))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Algebra.Group.Defs.«term_•_»
       (Term.app (Orientation.Analysis.InnerProductSpace.TwoDim.termω "ω") [`x `y])
       " • "
       `Complex.i)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `Complex.i
[PrettyPrinter.parenthesize] ...precedences are 73 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 73, term))
      (Term.app (Orientation.Analysis.InnerProductSpace.TwoDim.termω "ω") [`x `y])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `y
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `x
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (Orientation.Analysis.InnerProductSpace.TwoDim.termω "ω")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Orientation.Analysis.InnerProductSpace.TwoDim.termω', expected 'Orientation.Analysis.InnerProductSpace.TwoDim.termω._@.Analysis.InnerProductSpace.TwoDim._hyg.7'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.opaque'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.instance'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.axiom'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.example'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.inductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.classInductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.structure'-/-- failed to format: format: uncaught backtrack exception
theorem kahler_apply_apply ( x y : E ) : o . kahler x y = ⟪ x , y ⟫ + ω x y • Complex.i := rfl
#align orientation.kahler_apply_apply Orientation.kahler_apply_apply

theorem kahler_swap (x y : E) : o.kahler x y = conj (o.kahler y x) :=
  by
  simp only [kahler_apply_apply]
  rw [real_inner_comm, area_form_swap]
  simp
#align orientation.kahler_swap Orientation.kahler_swap

@[simp]
theorem kahler_apply_self (x : E) : o.kahler x x = ‖x‖ ^ 2 := by
  simp [kahler_apply_apply, real_inner_self_eq_norm_sq]
#align orientation.kahler_apply_self Orientation.kahler_apply_self

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers
      []
      [(Term.attributes "@[" [(Term.attrInstance (Term.attrKind []) (Attr.simp "simp" [] []))] "]")]
      []
      []
      []
      [])
     (Command.theorem
      "theorem"
      (Command.declId `kahler_right_angle_rotation_left [])
      (Command.declSig
       [(Term.explicitBinder "(" [`x `y] [":" `E] [] ")")]
       (Term.typeSpec
        ":"
        («term_=_»
         (Term.app
          (Term.proj `o "." `kahler)
          [(Term.app (Orientation.Analysis.InnerProductSpace.TwoDim.termJ "J") [`x]) `y])
         "="
         («term_*_» («term-_» "-" `Complex.i) "*" (Term.app (Term.proj `o "." `kahler) [`x `y])))))
      (Command.declValSimple
       ":="
       (Term.byTactic
        "by"
        (Tactic.tacticSeq
         (Tactic.tacticSeq1Indented
          [(Tactic.simp
            "simp"
            []
            []
            ["only"]
            ["["
             [(Tactic.simpLemma [] [] `o.area_form_right_angle_rotation_left)
              ","
              (Tactic.simpLemma [] [] `o.inner_right_angle_rotation_left)
              ","
              (Tactic.simpLemma [] [] `o.kahler_apply_apply)
              ","
              (Tactic.simpLemma [] [] `Complex.of_real_neg)
              ","
              (Tactic.simpLemma [] [] `Complex.real_smul)]
             "]"]
            [])
           []
           (Mathlib.Tactic.LinearCombination.linearCombination
            "linear_combination"
            []
            [(«term_*_»
              (Term.app (Orientation.Analysis.InnerProductSpace.TwoDim.termω "ω") [`x `y])
              "*"
              `Complex.I_sq)])])))
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
         [(Tactic.simp
           "simp"
           []
           []
           ["only"]
           ["["
            [(Tactic.simpLemma [] [] `o.area_form_right_angle_rotation_left)
             ","
             (Tactic.simpLemma [] [] `o.inner_right_angle_rotation_left)
             ","
             (Tactic.simpLemma [] [] `o.kahler_apply_apply)
             ","
             (Tactic.simpLemma [] [] `Complex.of_real_neg)
             ","
             (Tactic.simpLemma [] [] `Complex.real_smul)]
            "]"]
           [])
          []
          (Mathlib.Tactic.LinearCombination.linearCombination
           "linear_combination"
           []
           [(«term_*_»
             (Term.app (Orientation.Analysis.InnerProductSpace.TwoDim.termω "ω") [`x `y])
             "*"
             `Complex.I_sq)])])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Mathlib.Tactic.LinearCombination.linearCombination
       "linear_combination"
       []
       [(«term_*_»
         (Term.app (Orientation.Analysis.InnerProductSpace.TwoDim.termω "ω") [`x `y])
         "*"
         `Complex.I_sq)])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_*_»
       (Term.app (Orientation.Analysis.InnerProductSpace.TwoDim.termω "ω") [`x `y])
       "*"
       `Complex.I_sq)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `Complex.I_sq
[PrettyPrinter.parenthesize] ...precedences are 71 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 70, term))
      (Term.app (Orientation.Analysis.InnerProductSpace.TwoDim.termω "ω") [`x `y])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `y
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `x
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (Orientation.Analysis.InnerProductSpace.TwoDim.termω "ω")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Orientation.Analysis.InnerProductSpace.TwoDim.termω', expected 'Orientation.Analysis.InnerProductSpace.TwoDim.termω._@.Analysis.InnerProductSpace.TwoDim._hyg.7'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.declValSimple', expected 'Lean.Parser.Command.declValEqns'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.declValSimple', expected 'Lean.Parser.Command.whereStructInst'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.opaque'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.instance'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.axiom'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.example'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.inductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.classInductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.structure'-/-- failed to format: format: uncaught backtrack exception
@[ simp ]
  theorem
    kahler_right_angle_rotation_left
    ( x y : E ) : o . kahler J x y = - Complex.i * o . kahler x y
    :=
      by
        simp
            only
            [
              o.area_form_right_angle_rotation_left
                ,
                o.inner_right_angle_rotation_left
                ,
                o.kahler_apply_apply
                ,
                Complex.of_real_neg
                ,
                Complex.real_smul
              ]
          linear_combination ω x y * Complex.I_sq
#align orientation.kahler_right_angle_rotation_left Orientation.kahler_right_angle_rotation_left

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers
      []
      [(Term.attributes "@[" [(Term.attrInstance (Term.attrKind []) (Attr.simp "simp" [] []))] "]")]
      []
      []
      []
      [])
     (Command.theorem
      "theorem"
      (Command.declId `kahler_right_angle_rotation_right [])
      (Command.declSig
       [(Term.explicitBinder "(" [`x `y] [":" `E] [] ")")]
       (Term.typeSpec
        ":"
        («term_=_»
         (Term.app
          (Term.proj `o "." `kahler)
          [`x (Term.app (Orientation.Analysis.InnerProductSpace.TwoDim.termJ "J") [`y])])
         "="
         («term_*_» `Complex.i "*" (Term.app (Term.proj `o "." `kahler) [`x `y])))))
      (Command.declValSimple
       ":="
       (Term.byTactic
        "by"
        (Tactic.tacticSeq
         (Tactic.tacticSeq1Indented
          [(Tactic.simp
            "simp"
            []
            []
            ["only"]
            ["["
             [(Tactic.simpLemma [] [] `o.area_form_right_angle_rotation_right)
              ","
              (Tactic.simpLemma [] [] `o.inner_right_angle_rotation_right)
              ","
              (Tactic.simpLemma [] [] `o.kahler_apply_apply)
              ","
              (Tactic.simpLemma [] [] `Complex.of_real_neg)
              ","
              (Tactic.simpLemma [] [] `Complex.real_smul)]
             "]"]
            [])
           []
           (Mathlib.Tactic.LinearCombination.linearCombination
            "linear_combination"
            []
            [(«term_*_»
              («term-_»
               "-"
               (Term.app (Orientation.Analysis.InnerProductSpace.TwoDim.termω "ω") [`x `y]))
              "*"
              `Complex.I_sq)])])))
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
         [(Tactic.simp
           "simp"
           []
           []
           ["only"]
           ["["
            [(Tactic.simpLemma [] [] `o.area_form_right_angle_rotation_right)
             ","
             (Tactic.simpLemma [] [] `o.inner_right_angle_rotation_right)
             ","
             (Tactic.simpLemma [] [] `o.kahler_apply_apply)
             ","
             (Tactic.simpLemma [] [] `Complex.of_real_neg)
             ","
             (Tactic.simpLemma [] [] `Complex.real_smul)]
            "]"]
           [])
          []
          (Mathlib.Tactic.LinearCombination.linearCombination
           "linear_combination"
           []
           [(«term_*_»
             («term-_»
              "-"
              (Term.app (Orientation.Analysis.InnerProductSpace.TwoDim.termω "ω") [`x `y]))
             "*"
             `Complex.I_sq)])])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Mathlib.Tactic.LinearCombination.linearCombination
       "linear_combination"
       []
       [(«term_*_»
         («term-_» "-" (Term.app (Orientation.Analysis.InnerProductSpace.TwoDim.termω "ω") [`x `y]))
         "*"
         `Complex.I_sq)])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_*_»
       («term-_» "-" (Term.app (Orientation.Analysis.InnerProductSpace.TwoDim.termω "ω") [`x `y]))
       "*"
       `Complex.I_sq)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `Complex.I_sq
[PrettyPrinter.parenthesize] ...precedences are 71 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 70, term))
      («term-_» "-" (Term.app (Orientation.Analysis.InnerProductSpace.TwoDim.termω "ω") [`x `y]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app (Orientation.Analysis.InnerProductSpace.TwoDim.termω "ω") [`x `y])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `y
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `x
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (Orientation.Analysis.InnerProductSpace.TwoDim.termω "ω")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Orientation.Analysis.InnerProductSpace.TwoDim.termω', expected 'Orientation.Analysis.InnerProductSpace.TwoDim.termω._@.Analysis.InnerProductSpace.TwoDim._hyg.7'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.declValSimple', expected 'Lean.Parser.Command.declValEqns'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.declValSimple', expected 'Lean.Parser.Command.whereStructInst'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.opaque'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.instance'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.axiom'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.example'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.inductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.classInductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.structure'-/-- failed to format: format: uncaught backtrack exception
@[ simp ]
  theorem
    kahler_right_angle_rotation_right
    ( x y : E ) : o . kahler x J y = Complex.i * o . kahler x y
    :=
      by
        simp
            only
            [
              o.area_form_right_angle_rotation_right
                ,
                o.inner_right_angle_rotation_right
                ,
                o.kahler_apply_apply
                ,
                Complex.of_real_neg
                ,
                Complex.real_smul
              ]
          linear_combination - ω x y * Complex.I_sq
#align orientation.kahler_right_angle_rotation_right Orientation.kahler_right_angle_rotation_right

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers
      []
      [(Term.attributes "@[" [(Term.attrInstance (Term.attrKind []) (Attr.simp "simp" [] []))] "]")]
      []
      []
      []
      [])
     (Command.theorem
      "theorem"
      (Command.declId `kahler_comp_right_angle_rotation [])
      (Command.declSig
       [(Term.explicitBinder "(" [`x `y] [":" `E] [] ")")]
       (Term.typeSpec
        ":"
        («term_=_»
         (Term.app
          (Term.proj `o "." `kahler)
          [(Term.app (Orientation.Analysis.InnerProductSpace.TwoDim.termJ "J") [`x])
           (Term.app (Orientation.Analysis.InnerProductSpace.TwoDim.termJ "J") [`y])])
         "="
         (Term.app (Term.proj `o "." `kahler) [`x `y]))))
      (Command.declValSimple
       ":="
       (Term.byTactic
        "by"
        (Tactic.tacticSeq
         (Tactic.tacticSeq1Indented
          [(Tactic.simp
            "simp"
            []
            []
            ["only"]
            ["["
             [(Tactic.simpLemma [] [] `kahler_right_angle_rotation_left)
              ","
              (Tactic.simpLemma [] [] `kahler_right_angle_rotation_right)]
             "]"]
            [])
           []
           (Mathlib.Tactic.LinearCombination.linearCombination
            "linear_combination"
            []
            [(«term_*_» («term-_» "-" (Term.app `o.kahler [`x `y])) "*" `Complex.I_sq)])])))
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
         [(Tactic.simp
           "simp"
           []
           []
           ["only"]
           ["["
            [(Tactic.simpLemma [] [] `kahler_right_angle_rotation_left)
             ","
             (Tactic.simpLemma [] [] `kahler_right_angle_rotation_right)]
            "]"]
           [])
          []
          (Mathlib.Tactic.LinearCombination.linearCombination
           "linear_combination"
           []
           [(«term_*_» («term-_» "-" (Term.app `o.kahler [`x `y])) "*" `Complex.I_sq)])])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Mathlib.Tactic.LinearCombination.linearCombination
       "linear_combination"
       []
       [(«term_*_» («term-_» "-" (Term.app `o.kahler [`x `y])) "*" `Complex.I_sq)])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_*_» («term-_» "-" (Term.app `o.kahler [`x `y])) "*" `Complex.I_sq)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `Complex.I_sq
[PrettyPrinter.parenthesize] ...precedences are 71 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 70, term))
      («term-_» "-" (Term.app `o.kahler [`x `y]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `o.kahler [`x `y])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `y
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `x
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `o.kahler
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 75 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 70 >? 75, (some 75, term) <=? (some 70, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 70, (some 71, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.simp
       "simp"
       []
       []
       ["only"]
       ["["
        [(Tactic.simpLemma [] [] `kahler_right_angle_rotation_left)
         ","
         (Tactic.simpLemma [] [] `kahler_right_angle_rotation_right)]
        "]"]
       [])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `kahler_right_angle_rotation_right
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `kahler_right_angle_rotation_left
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, tactic) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
      («term_=_»
       (Term.app
        (Term.proj `o "." `kahler)
        [(Term.app (Orientation.Analysis.InnerProductSpace.TwoDim.termJ "J") [`x])
         (Term.app (Orientation.Analysis.InnerProductSpace.TwoDim.termJ "J") [`y])])
       "="
       (Term.app (Term.proj `o "." `kahler) [`x `y]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app (Term.proj `o "." `kahler) [`x `y])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `y
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `x
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (Term.proj `o "." `kahler)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `o
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 50, term))
      (Term.app
       (Term.proj `o "." `kahler)
       [(Term.app (Orientation.Analysis.InnerProductSpace.TwoDim.termJ "J") [`x])
        (Term.app (Orientation.Analysis.InnerProductSpace.TwoDim.termJ "J") [`y])])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app (Orientation.Analysis.InnerProductSpace.TwoDim.termJ "J") [`y])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `y
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (Orientation.Analysis.InnerProductSpace.TwoDim.termJ "J")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Orientation.Analysis.InnerProductSpace.TwoDim.termJ', expected 'Orientation.Analysis.InnerProductSpace.TwoDim.termJ._@.Analysis.InnerProductSpace.TwoDim._hyg.50'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.opaque'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.instance'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.axiom'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.example'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.inductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.classInductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.structure'-/-- failed to format: format: uncaught backtrack exception
@[ simp ]
  theorem
    kahler_comp_right_angle_rotation
    ( x y : E ) : o . kahler J x J y = o . kahler x y
    :=
      by
        simp only [ kahler_right_angle_rotation_left , kahler_right_angle_rotation_right ]
          linear_combination - o.kahler x y * Complex.I_sq
#align orientation.kahler_comp_right_angle_rotation Orientation.kahler_comp_right_angle_rotation

@[simp]
theorem kahler_neg_orientation (x y : E) : (-o).kahler x y = conj (o.kahler x y) := by
  simp [kahler_apply_apply]
#align orientation.kahler_neg_orientation Orientation.kahler_neg_orientation

theorem kahler_mul (a x y : E) : o.kahler x a * o.kahler a y = ‖a‖ ^ 2 * o.kahler x y :=
  by
  trans (↑(‖a‖ ^ 2) : ℂ) * o.kahler x y
  · ext
    · simp only [o.kahler_apply_apply, Complex.add_im, Complex.add_re, Complex.I_im, Complex.I_re,
        Complex.mul_im, Complex.mul_re, Complex.of_real_im, Complex.of_real_re, Complex.real_smul]
      rw [real_inner_comm a x, o.area_form_swap x a]
      linear_combination o.inner_mul_inner_add_area_form_mul_area_form a x y
    · simp only [o.kahler_apply_apply, Complex.add_im, Complex.add_re, Complex.I_im, Complex.I_re,
        Complex.mul_im, Complex.mul_re, Complex.of_real_im, Complex.of_real_re, Complex.real_smul]
      rw [real_inner_comm a x, o.area_form_swap x a]
      linear_combination o.inner_mul_area_form_sub a x y
  · norm_cast
#align orientation.kahler_mul Orientation.kahler_mul

theorem norm_sq_kahler (x y : E) : Complex.normSq (o.kahler x y) = ‖x‖ ^ 2 * ‖y‖ ^ 2 := by
  simpa [kahler_apply_apply, Complex.normSq, sq] using o.inner_sq_add_area_form_sq x y
#align orientation.norm_sq_kahler Orientation.norm_sq_kahler

theorem abs_kahler (x y : E) : Complex.abs (o.kahler x y) = ‖x‖ * ‖y‖ :=
  by
  rw [← sq_eq_sq, Complex.sq_abs]
  · linear_combination o.norm_sq_kahler x y
  · positivity
  · positivity
#align orientation.abs_kahler Orientation.abs_kahler

theorem norm_kahler (x y : E) : ‖o.kahler x y‖ = ‖x‖ * ‖y‖ := by simpa using o.abs_kahler x y
#align orientation.norm_kahler Orientation.norm_kahler

theorem eq_zero_or_eq_zero_of_kahler_eq_zero {x y : E} (hx : o.kahler x y = 0) : x = 0 ∨ y = 0 :=
  by
  have : ‖x‖ * ‖y‖ = 0 := by simpa [hx] using (o.norm_kahler x y).symm
  cases' eq_zero_or_eq_zero_of_mul_eq_zero this with h h
  · left
    simpa using h
  · right
    simpa using h
#align
  orientation.eq_zero_or_eq_zero_of_kahler_eq_zero Orientation.eq_zero_or_eq_zero_of_kahler_eq_zero

theorem kahler_eq_zero_iff (x y : E) : o.kahler x y = 0 ↔ x = 0 ∨ y = 0 :=
  by
  refine' ⟨o.eq_zero_or_eq_zero_of_kahler_eq_zero, _⟩
  rintro (rfl | rfl) <;> simp
#align orientation.kahler_eq_zero_iff Orientation.kahler_eq_zero_iff

theorem kahler_ne_zero {x y : E} (hx : x ≠ 0) (hy : y ≠ 0) : o.kahler x y ≠ 0 :=
  by
  apply mt o.eq_zero_or_eq_zero_of_kahler_eq_zero
  tauto
#align orientation.kahler_ne_zero Orientation.kahler_ne_zero

theorem kahler_ne_zero_iff (x y : E) : o.kahler x y ≠ 0 ↔ x ≠ 0 ∧ y ≠ 0 :=
  by
  refine' ⟨_, fun h => o.kahler_ne_zero h.1 h.2⟩
  contrapose
  simp only [not_and_or, not_not, kahler_apply_apply, Complex.real_smul]
  rintro (rfl | rfl) <;> simp
#align orientation.kahler_ne_zero_iff Orientation.kahler_ne_zero_iff

theorem kahler_map {F : Type _} [InnerProductSpace ℝ F] [Fact (finrank ℝ F = 2)] (φ : E ≃ₗᵢ[ℝ] F)
    (x y : F) :
    (Orientation.map (Fin 2) φ.toLinearEquiv o).kahler x y = o.kahler (φ.symm x) (φ.symm y) := by
  simp [kahler_apply_apply, area_form_map]
#align orientation.kahler_map Orientation.kahler_map

/-- The bilinear map `kahler` is invariant under pullback by a positively-oriented isometric
automorphism. -/
theorem kahler_comp_linear_isometry_equiv (φ : E ≃ₗᵢ[ℝ] E)
    (hφ : 0 < (φ.toLinearEquiv : E →ₗ[ℝ] E).det) (x y : E) : o.kahler (φ x) (φ y) = o.kahler x y :=
  by simp [kahler_apply_apply, o.area_form_comp_linear_isometry_equiv φ hφ]
#align orientation.kahler_comp_linear_isometry_equiv Orientation.kahler_comp_linear_isometry_equiv

end Orientation

namespace Complex

attribute [local instance] Complex.finrank_real_complex_fact

@[simp]
protected theorem area_form (w z : ℂ) : Complex.orientation.areaForm w z = (conj w * z).im :=
  by
  let o := Complex.orientation
  simp only [o.area_form_to_volume_form, o.volume_form_robust Complex.orthonormalBasisOneI rfl,
    Basis.det_apply, Matrix.det_fin_two, Basis.to_matrix_apply, to_basis_orthonormal_basis_one_I,
    Matrix.cons_val_zero, coe_basis_one_I_repr, Matrix.cons_val_one, Matrix.head_cons, mul_im,
    conj_re, conj_im]
  ring
#align complex.area_form Complex.area_form

@[simp]
protected theorem right_angle_rotation (z : ℂ) : Complex.orientation.rightAngleRotation z = I * z :=
  by
  apply ext_inner_right ℝ
  intro w
  rw [Orientation.inner_right_angle_rotation_left]
  simp only [Complex.area_form, Complex.inner, mul_re, mul_im, conj_re, conj_im, map_mul, conj_I,
    neg_re, neg_im, I_re, I_im]
  ring
#align complex.right_angle_rotation Complex.right_angle_rotation

@[simp]
protected theorem kahler (w z : ℂ) : Complex.orientation.kahler w z = conj w * z :=
  by
  rw [Orientation.kahler_apply_apply]
  ext1 <;> simp
#align complex.kahler Complex.kahler

end Complex

namespace Orientation

-- mathport name: exprω
local notation "ω" => o.areaForm

-- mathport name: exprJ
local notation "J" => o.rightAngleRotation

open Complex

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers
      [(Command.docComment
        "/--"
        "The area form on an oriented real inner product space of dimension 2 can be evaluated in terms\nof a complex-number representation of the space. -/")]
      []
      []
      []
      []
      [])
     (Command.theorem
      "theorem"
      (Command.declId `area_form_map_complex [])
      (Command.declSig
       [(Term.explicitBinder
         "("
         [`f]
         [":"
          (Analysis.NormedSpace.LinearIsometry.«term_≃ₗᵢ[_]_»
           `E
           " ≃ₗᵢ["
           (Data.Real.Basic.termℝ "ℝ")
           "] "
           (Data.Complex.Basic.termℂ "ℂ"))]
         []
         ")")
        (Term.explicitBinder
         "("
         [`hf]
         [":"
          («term_=_»
           (Term.app
            `Orientation.map
            [(Term.app `Fin [(num "2")]) (Term.proj `f "." `toLinearEquiv) `o])
           "="
           `Complex.orientation)]
         []
         ")")
        (Term.explicitBinder "(" [`x `y] [":" `E] [] ")")]
       (Term.typeSpec
        ":"
        («term_=_»
         (Term.app (Orientation.Analysis.InnerProductSpace.TwoDim.termω_1 "ω") [`x `y])
         "="
         (Term.proj
          («term_*_»
           (Term.app
            (ComplexConjugate.Algebra.Star.Basic.star_ring_end "conj")
            [(Term.app `f [`x])])
           "*"
           (Term.app `f [`y]))
          "."
          `im))))
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
             [(Tactic.rwRule [(patternIgnore (token.«← » "←"))] `Complex.area_form)
              ","
              (Tactic.rwRule [(patternIgnore (token.«← » "←"))] `hf)
              ","
              (Tactic.rwRule [] `o.area_form_map)]
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
            [(Tactic.rwRule [(patternIgnore (token.«← » "←"))] `Complex.area_form)
             ","
             (Tactic.rwRule [(patternIgnore (token.«← » "←"))] `hf)
             ","
             (Tactic.rwRule [] `o.area_form_map)]
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
        [(Tactic.rwRule [(patternIgnore (token.«← » "←"))] `Complex.area_form)
         ","
         (Tactic.rwRule [(patternIgnore (token.«← » "←"))] `hf)
         ","
         (Tactic.rwRule [] `o.area_form_map)]
        "]")
       [])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `o.area_form_map
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `hf
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `Complex.area_form
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, tactic) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
      («term_=_»
       (Term.app (Orientation.Analysis.InnerProductSpace.TwoDim.termω_1 "ω") [`x `y])
       "="
       (Term.proj
        («term_*_»
         (Term.app (ComplexConjugate.Algebra.Star.Basic.star_ring_end "conj") [(Term.app `f [`x])])
         "*"
         (Term.app `f [`y]))
        "."
        `im))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.proj
       («term_*_»
        (Term.app (ComplexConjugate.Algebra.Star.Basic.star_ring_end "conj") [(Term.app `f [`x])])
        "*"
        (Term.app `f [`y]))
       "."
       `im)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      («term_*_»
       (Term.app (ComplexConjugate.Algebra.Star.Basic.star_ring_end "conj") [(Term.app `f [`x])])
       "*"
       (Term.app `f [`y]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `f [`y])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `y
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `f
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
[PrettyPrinter.parenthesize] ...precedences are 0 >? 70, (some 71, term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     («term_*_»
      (Term.app
       (ComplexConjugate.Algebra.Star.Basic.star_ring_end "conj")
       [(Term.paren "(" (Term.app `f [`x]) ")")])
      "*"
      (Term.app `f [`y]))
     ")")
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 50, term))
      (Term.app (Orientation.Analysis.InnerProductSpace.TwoDim.termω_1 "ω") [`x `y])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `y
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `x
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (Orientation.Analysis.InnerProductSpace.TwoDim.termω_1 "ω")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Orientation.Analysis.InnerProductSpace.TwoDim.termω_1', expected 'Orientation.Analysis.InnerProductSpace.TwoDim.termω_1._@.Analysis.InnerProductSpace.TwoDim._hyg.93'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.opaque'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.instance'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.axiom'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.example'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.inductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.classInductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.structure'-/-- failed to format: format: uncaught backtrack exception
/--
    The area form on an oriented real inner product space of dimension 2 can be evaluated in terms
    of a complex-number representation of the space. -/
  theorem
    area_form_map_complex
    ( f : E ≃ₗᵢ[ ℝ ] ℂ )
        ( hf : Orientation.map Fin 2 f . toLinearEquiv o = Complex.orientation )
        ( x y : E )
      : ω x y = conj f x * f y . im
    := by rw [ ← Complex.area_form , ← hf , o.area_form_map ] simp
#align orientation.area_form_map_complex Orientation.area_form_map_complex

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers
      [(Command.docComment
        "/--"
        "The rotation by 90 degrees on an oriented real inner product space of dimension 2 can be\nevaluated in terms of a complex-number representation of the space. -/")]
      []
      []
      []
      []
      [])
     (Command.theorem
      "theorem"
      (Command.declId `right_angle_rotation_map_complex [])
      (Command.declSig
       [(Term.explicitBinder
         "("
         [`f]
         [":"
          (Analysis.NormedSpace.LinearIsometry.«term_≃ₗᵢ[_]_»
           `E
           " ≃ₗᵢ["
           (Data.Real.Basic.termℝ "ℝ")
           "] "
           (Data.Complex.Basic.termℂ "ℂ"))]
         []
         ")")
        (Term.explicitBinder
         "("
         [`hf]
         [":"
          («term_=_»
           (Term.app
            `Orientation.map
            [(Term.app `Fin [(num "2")]) (Term.proj `f "." `toLinearEquiv) `o])
           "="
           `Complex.orientation)]
         []
         ")")
        (Term.explicitBinder "(" [`x] [":" `E] [] ")")]
       (Term.typeSpec
        ":"
        («term_=_»
         (Term.app `f [(Term.app (Orientation.Analysis.InnerProductSpace.TwoDim.termJ_1 "J") [`x])])
         "="
         («term_*_» `I "*" (Term.app `f [`x])))))
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
             [(Tactic.rwRule [(patternIgnore (token.«← » "←"))] `Complex.right_angle_rotation)
              ","
              (Tactic.rwRule [(patternIgnore (token.«← » "←"))] `hf)
              ","
              (Tactic.rwRule [] `o.right_angle_rotation_map)]
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
            [(Tactic.rwRule [(patternIgnore (token.«← » "←"))] `Complex.right_angle_rotation)
             ","
             (Tactic.rwRule [(patternIgnore (token.«← » "←"))] `hf)
             ","
             (Tactic.rwRule [] `o.right_angle_rotation_map)]
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
        [(Tactic.rwRule [(patternIgnore (token.«← » "←"))] `Complex.right_angle_rotation)
         ","
         (Tactic.rwRule [(patternIgnore (token.«← » "←"))] `hf)
         ","
         (Tactic.rwRule [] `o.right_angle_rotation_map)]
        "]")
       [])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `o.right_angle_rotation_map
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `hf
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `Complex.right_angle_rotation
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, tactic) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
      («term_=_»
       (Term.app `f [(Term.app (Orientation.Analysis.InnerProductSpace.TwoDim.termJ_1 "J") [`x])])
       "="
       («term_*_» `I "*" (Term.app `f [`x])))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_*_» `I "*" (Term.app `f [`x]))
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
[PrettyPrinter.parenthesize] ...precedences are 71 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 70, term))
      `I
[PrettyPrinter.parenthesize] ...precedences are 70 >? 1024, (none, [anonymous]) <=? (some 70, term)
[PrettyPrinter.parenthesize] ...precedences are 51 >? 70, (some 71, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 50, term))
      (Term.app `f [(Term.app (Orientation.Analysis.InnerProductSpace.TwoDim.termJ_1 "J") [`x])])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app (Orientation.Analysis.InnerProductSpace.TwoDim.termJ_1 "J") [`x])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `x
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (Orientation.Analysis.InnerProductSpace.TwoDim.termJ_1 "J")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Orientation.Analysis.InnerProductSpace.TwoDim.termJ_1', expected 'Orientation.Analysis.InnerProductSpace.TwoDim.termJ_1._@.Analysis.InnerProductSpace.TwoDim._hyg.132'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.opaque'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.instance'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.axiom'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.example'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.inductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.classInductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.structure'-/-- failed to format: format: uncaught backtrack exception
/--
    The rotation by 90 degrees on an oriented real inner product space of dimension 2 can be
    evaluated in terms of a complex-number representation of the space. -/
  theorem
    right_angle_rotation_map_complex
    ( f : E ≃ₗᵢ[ ℝ ] ℂ )
        ( hf : Orientation.map Fin 2 f . toLinearEquiv o = Complex.orientation )
        ( x : E )
      : f J x = I * f x
    := by rw [ ← Complex.right_angle_rotation , ← hf , o.right_angle_rotation_map ] simp
#align orientation.right_angle_rotation_map_complex Orientation.right_angle_rotation_map_complex

/-- The Kahler form on an oriented real inner product space of dimension 2 can be evaluated in terms
of a complex-number representation of the space. -/
theorem kahler_map_complex (f : E ≃ₗᵢ[ℝ] ℂ)
    (hf : Orientation.map (Fin 2) f.toLinearEquiv o = Complex.orientation) (x y : E) :
    o.kahler x y = conj (f x) * f y :=
  by
  rw [← Complex.kahler, ← hf, o.kahler_map]
  simp
#align orientation.kahler_map_complex Orientation.kahler_map_complex

end Orientation

